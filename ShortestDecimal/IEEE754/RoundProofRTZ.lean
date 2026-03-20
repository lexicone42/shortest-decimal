/-
  IEEE754/RoundProofRTZ.lean

  Proof of the projection property for round-toward-zero:
    roundTowardZero(toRat(x)) = x  for all finite x

  This is simpler than the RNE proof because toRat(x) is exactly
  representable, so floor(sigExact) = effectiveSignificand -- no
  tie-breaking analysis is needed.
-/
import ShortestDecimal.IEEE754.RoundTowardZero
import ShortestDecimal.IEEE754.RoundProof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

namespace F64

/-- For zero, toRat is 0 and roundTowardZero(0) = posZero. -/
theorem round_rtz_zero : roundTowardZero 0 = posZero := by
  simp [roundTowardZero]

theorem round_rtz_idempotent_posZero : roundTowardZero posZero.toRat = posZero := by
  rw [toRat_posZero]; exact round_rtz_zero

theorem round_rtz_idempotent_negZero : roundTowardZero negZero.toRat = posZero := by
  rw [toRat_negZero]; exact round_rtz_zero

/-! ## Key lemma: sigExact is a natural number for representable values -/

/-- The scaled significand for a representable F64 is exactly a natural number. -/
private theorem sigExact_eq_rtz (x : F64) (hfin : x.isFinite) (_hne : x.toRat ≠ 0) :
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

/-! ## roundSignificand_rtz exactness -/

/-- roundSignificand_rtz recovers the mantissa exactly with no bump
    when sigExact is a natural number (as it is for any representable value). -/
theorem roundSignificand_rtz_exact (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundSignificand_rtz |x.toRat| x.biasedExp.val = (x.mantissa.val, false) := by
  unfold roundSignificand_rtz
  simp only []
  have hse := sigExact_eq_rtz x hfin hne
  simp only [] at hse
  rw [hse]
  rw [floor_nat_cast]
  simp only [Int.toNat_natCast]
  have hm := x.mantissa.isLt
  by_cases hbv : x.biasedExp.val = 0
  · rw [esig_subnormal x hbv]
    simp only [hbv, ↓reduceIte]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · rw [esig_normal x hbv]
    simp only [show ¬(x.biasedExp.val = 0) from hbv, ↓reduceIte]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]
        constructor
        · omega
        · trivial

/-! ## Main composition -/

/-- roundTowardZero(x.toRat) = x for finite non-zero x. -/
theorem round_rtz_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundTowardZero (x.toRat) = x := by
  unfold roundTowardZero
  rw [if_neg hne]
  simp only []
  have hfbe := findBiasedExp_correct x hfin hne
  have hrs := roundSignificand_rtz_exact x hfin hne
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

/-- roundTowardZero is idempotent on all finite F64 values:
    roundTowardZero(toRat(x)) = x  (up to signed zero collapsing). -/
theorem round_rtz_idempotent (x : F64) (hfin : x.isFinite) :
    roundTowardZero (x.toRat) = x ∨
    (x.toRat = 0 ∧ roundTowardZero (x.toRat) = posZero) := by
  by_cases hne : x.toRat = 0
  · right; exact ⟨hne, by rw [hne]; exact round_rtz_zero⟩
  · left; exact round_rtz_nonzero x hfin hne

end F64
