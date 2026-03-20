/-
  IEEE754/RoundProofRNA.lean

  Proof of the projection property for round-to-nearest-ties-to-away:
    roundTiesAway(toRat(x)) = x  for all finite x

  This is simpler than the RNE proof because toRat(x) is exactly
  representable, so remainder = 0 and no tie-breaking is needed.
  The RNA and RNE rounding functions agree on non-tie inputs.
-/
import ShortestDecimal.IEEE754.RoundTiesAway
import ShortestDecimal.IEEE754.RoundProof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

namespace F64

/-- For zero, toRat is 0 and roundTiesAway(0) = posZero. -/
theorem round_rna_zero : roundTiesAway 0 = posZero := by
  simp [roundTiesAway]

theorem round_rna_idempotent_posZero : roundTiesAway posZero.toRat = posZero := by
  rw [toRat_posZero]; exact round_rna_zero

theorem round_rna_idempotent_negZero : roundTiesAway negZero.toRat = posZero := by
  rw [toRat_negZero]; exact round_rna_zero

/-! ## Key lemma: sigExact is a natural number for representable values -/

/-- The scaled significand for a representable F64 is exactly a natural number.
    (Reuses the same proof structure as RNE/RTZ.) -/
private theorem sigExact_eq_rna (x : F64) (hfin : x.isFinite) (_hne : x.toRat ≠ 0) :
    let binExp : Int := if x.biasedExp.val = 0 then -1074 else (x.biasedExp.val : Int) - 1075
    (if binExp ≥ 0 then |x.toRat| / (2 ^ binExp.toNat : ℚ)
     else |x.toRat| * (2 ^ (-binExp).toNat : ℚ)) =
    (x.effectiveSignificand : ℚ) := by
  simp only []
  rw [binExp_eq, toRat_abs x hfin]
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    exact mul_div_cancel_right₀ _ (ne_of_gt (by positivity))
  · simp only [if_neg hexp]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity))

/-! ## roundSignificand_rna exactness -/

/-- roundSignificand_rna recovers the mantissa exactly with no bump
    when sigExact is a natural number (remainder = 0 < 1/2). -/
theorem roundSignificand_rna_exact (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundSignificand_rna |x.toRat| x.biasedExp.val = (x.mantissa.val, false) := by
  unfold roundSignificand_rna
  simp only []
  have hse := sigExact_eq_rna x hfin hne
  simp only [] at hse
  rw [hse]
  rw [floor_nat_cast]
  simp only [Int.toNat_natCast]
  -- remainder = effectiveSignificand - effectiveSignificand = 0 < 1/2
  simp only [sub_self]
  norm_num
  have hm := x.mantissa.isLt
  split
  · next hbe =>
    have hbv : x.biasedExp.val = 0 := by simpa using congrArg Fin.val hbe
    rw [esig_subnormal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · next hbe =>
    have hbv : x.biasedExp.val ≠ 0 := fun h => hbe (Fin.ext h)
    rw [esig_normal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]
        constructor
        · omega
        · trivial

/-! ## Main composition -/

/-- roundTiesAway(x.toRat) = x for finite non-zero x. -/
theorem round_rna_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundTiesAway (x.toRat) = x := by
  unfold roundTiesAway
  rw [if_neg hne]
  simp only []
  have hfbe := findBiasedExp_correct x hfin hne
  have hrs := roundSignificand_rna_exact x hfin hne
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  rw [hfbe, hrs]
  simp only []
  split
  · next h => exact absurd h (by decide)
  · split
    · next h => exfalso; unfold maxBiasedExp at h; omega
    · split
      · next hmk =>
        have hdec : decide (x.toRat < 0) = x.sign := by
          cases hs : x.sign
          · exact decide_eq_false (mt hsign.mp (by simp [hs]))
          · exact decide_eq_true (hsign.mpr hs)
        unfold mkFinite at hmk
        simp only [show x.biasedExp.val < 2047 from hexp_lt,
                   show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true] at hmk
        rw [hdec] at hmk
        simp only [Option.some.injEq] at hmk
        rw [← hmk]
      · next hmk =>
        exfalso; unfold mkFinite at hmk
        simp [show x.biasedExp.val < 2047 from hexp_lt] at hmk

/-- roundTiesAway is idempotent on all finite F64 values:
    roundTiesAway(toRat(x)) = x  (up to signed zero collapsing). -/
theorem round_rna_idempotent (x : F64) (hfin : x.isFinite) :
    roundTiesAway (x.toRat) = x ∨
    (x.toRat = 0 ∧ roundTiesAway (x.toRat) = posZero) := by
  by_cases hne : x.toRat = 0
  · right; exact ⟨hne, by rw [hne]; exact round_rna_zero⟩
  · left; exact round_rna_nonzero x hfin hne

end F64
