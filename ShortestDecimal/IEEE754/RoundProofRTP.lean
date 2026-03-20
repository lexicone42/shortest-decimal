/-
  IEEE754/RoundProofRTP.lean

  Proof of the projection property for round-toward-positive-infinity:
    roundTowardPos(toRat(x)) = x  for all finite x

  Key insight: toRat(x) is exactly representable, so remainder = 0.
  When remainder = 0, ceiling = floor = sigExact. Thus roundSignificand_rtp_up
  agrees with roundSignificand_rtz on exact inputs.
-/
import ShortestDecimal.IEEE754.RoundTowardPos
import ShortestDecimal.IEEE754.RoundProofRTZ
import ShortestDecimal.IEEE754.RoundProof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

namespace F64

/-- For zero, toRat is 0 and roundTowardPos(0) = posZero. -/
theorem round_rtp_zero : roundTowardPos 0 = posZero := by
  simp [roundTowardPos]

theorem round_rtp_idempotent_posZero : roundTowardPos posZero.toRat = posZero := by
  rw [toRat_posZero]; exact round_rtp_zero

theorem round_rtp_idempotent_negZero : roundTowardPos negZero.toRat = posZero := by
  rw [toRat_negZero]; exact round_rtp_zero

/-! ## Key lemma: rtp_up agrees with rtz on any input with zero remainder -/

/-- When the remainder (sigExact - floor(sigExact)) is zero, roundSignificand_rtp_up
    and roundSignificand_rtz agree. -/
theorem roundSignificand_rtp_up_eq_rtz (qAbs : ℚ) (bexp : Nat)
    (hrem : (let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
             let sigExact := if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
                             else qAbs * (2 ^ (-binExp).toNat : ℚ)
             sigExact - ↑sigExact.floor.toNat) = 0) :
    roundSignificand_rtp_up qAbs bexp = roundSignificand_rtz qAbs bexp := by
  simp only [] at hrem
  show roundSignificand_rtp_up qAbs bexp = roundSignificand_rtz qAbs bexp
  unfold roundSignificand_rtp_up
  simp only []
  -- The only difference between rtp_up and rtz is the ceiling step.
  -- When remainder = 0, `if remainder > 0 then sigFloor + 1 else sigFloor` = sigFloor.
  have hceil : ¬((if (if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075) ≥ 0
                  then qAbs / (2 : ℚ) ^ (if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075).toNat
                  else qAbs * (2 : ℚ) ^ (-(if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075)).toNat)
                - ↑(if (if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075) ≥ 0
                    then qAbs / (2 : ℚ) ^ (if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075).toNat
                    else qAbs * (2 : ℚ) ^ (-(if bexp = 0 then (-1074 : Int) else (bexp : Int) - 1075)).toNat).floor.toNat > 0) := by
    rw [hrem]; exact not_lt.mpr le_rfl
  simp only [hceil, ↓reduceIte]
  rfl

/-- For exact representable values, the remainder is zero. -/
private theorem remainder_zero_of_representable (x : F64) (hfin : x.isFinite) (_hne : x.toRat ≠ 0) :
    (let binExp : Int := if x.biasedExp.val = 0 then -1074 else (x.biasedExp.val : Int) - 1075
     let sigExact := if binExp ≥ 0 then |x.toRat| / (2 ^ binExp.toNat : ℚ)
                     else |x.toRat| * (2 ^ (-binExp).toNat : ℚ)
     sigExact - ↑sigExact.floor.toNat) = 0 := by
  simp only []
  rw [binExp_eq, toRat_abs x hfin]
  by_cases hexp : x.effectiveBinaryExp ≥ 0
  · simp only [if_pos hexp]
    have := mul_div_cancel_right₀ (x.effectiveSignificand : ℚ) (ne_of_gt (show (0 : ℚ) < 2 ^ x.effectiveBinaryExp.toNat from by positivity))
    rw [this, floor_nat_cast, Int.toNat_natCast, sub_self]
  · simp only [if_neg hexp]
    have := div_mul_cancel₀ (x.effectiveSignificand : ℚ) (ne_of_gt (show (0 : ℚ) < 2 ^ (-x.effectiveBinaryExp).toNat from by positivity))
    rw [this, floor_nat_cast, Int.toNat_natCast, sub_self]

/-- roundSignificand_rtp_up recovers the mantissa exactly with no bump
    when applied to a representable value. -/
theorem roundSignificand_rtp_up_exact (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundSignificand_rtp_up |x.toRat| x.biasedExp.val = (x.mantissa.val, false) := by
  rw [roundSignificand_rtp_up_eq_rtz _ _ (remainder_zero_of_representable x hfin hne)]
  exact roundSignificand_rtz_exact x hfin hne

/-! ## Main composition -/

/-- roundTowardPos(x.toRat) = x for finite non-zero x (positive case). -/
private theorem round_rtp_nonzero_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = false) :
    roundTowardPos (x.toRat) = x := by
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  have hfbe := findBiasedExp_correct x hfin hne
  have hpos : ¬(x.toRat < 0) := mt hsign.mp (by simp [hs])
  have hrs := roundSignificand_rtp_up_exact x hfin hne
  unfold roundTowardPos
  rw [if_neg hne]
  simp only [if_neg hpos, hfbe, hrs]
  simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold maxBiasedExp; omega)]
  unfold mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt,
             show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
  have hdec : decide (x.toRat < 0) = false := decide_eq_false hpos
  rw [hdec]
  rcases x with ⟨s, be, m⟩; simp only at hs; rw [hs]

/-- roundTowardPos(x.toRat) = x for finite non-zero x (negative case). -/
private theorem round_rtp_nonzero_neg (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = true) :
    roundTowardPos (x.toRat) = x := by
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  have hfbe := findBiasedExp_correct x hfin hne
  have hneg : x.toRat < 0 := hsign.mpr hs
  have hrs := roundSignificand_rtz_exact x hfin hne
  unfold roundTowardPos
  rw [if_neg hne]
  simp only [if_pos hneg, hfbe, hrs]
  simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold maxBiasedExp; omega)]
  unfold mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt,
             show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
  have hdec : decide (x.toRat < 0) = true := decide_eq_true hneg
  rw [hdec]
  rcases x with ⟨s, be, m⟩; simp only at hs; rw [hs]

/-- roundTowardPos(x.toRat) = x for finite non-zero x. -/
theorem round_rtp_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundTowardPos (x.toRat) = x := by
  cases hs : x.sign
  · exact round_rtp_nonzero_pos x hfin hne hs
  · exact round_rtp_nonzero_neg x hfin hne hs

/-- roundTowardPos is idempotent on all finite F64 values:
    roundTowardPos(toRat(x)) = x  (up to signed zero collapsing). -/
theorem round_rtp_idempotent (x : F64) (hfin : x.isFinite) :
    roundTowardPos (x.toRat) = x ∨
    (x.toRat = 0 ∧ roundTowardPos (x.toRat) = posZero) := by
  by_cases hne : x.toRat = 0
  · right; exact ⟨hne, by rw [hne]; exact round_rtp_zero⟩
  · left; exact round_rtp_nonzero x hfin hne

end F64
