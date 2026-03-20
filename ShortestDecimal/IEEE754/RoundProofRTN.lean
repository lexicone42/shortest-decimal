/-
  IEEE754/RoundProofRTN.lean

  Proof of the projection property for round-toward-negative-infinity:
    roundTowardNeg(toRat(x)) = x  for all finite x

  Key insight: toRat(x) is exactly representable, so remainder = 0.
  For positive x, roundSignificand_rtz is used (floor).
  For negative x, roundSignificand_rtp_up is used (ceiling of magnitude).
  Both give the same result as rtz on exact inputs since remainder = 0.
-/
import ShortestDecimal.IEEE754.RoundTowardNeg
import ShortestDecimal.IEEE754.RoundProofRTP
import ShortestDecimal.IEEE754.RoundProofRTZ
import ShortestDecimal.IEEE754.RoundProof
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

namespace F64

/-- For zero, toRat is 0 and roundTowardNeg(0) = posZero. -/
theorem round_rtn_zero : roundTowardNeg 0 = posZero := by
  simp [roundTowardNeg]

theorem round_rtn_idempotent_posZero : roundTowardNeg posZero.toRat = posZero := by
  rw [toRat_posZero]; exact round_rtn_zero

theorem round_rtn_idempotent_negZero : roundTowardNeg negZero.toRat = posZero := by
  rw [toRat_negZero]; exact round_rtn_zero

/-! ## Main composition -/

/-- roundTowardNeg(x.toRat) = x for finite non-zero x (positive case). -/
private theorem round_rtn_nonzero_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = false) :
    roundTowardNeg (x.toRat) = x := by
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  have hfbe := findBiasedExp_correct x hfin hne
  have hpos : ¬(x.toRat < 0) := mt hsign.mp (by simp [hs])
  have hrs := roundSignificand_rtz_exact x hfin hne
  unfold roundTowardNeg
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

/-- roundTowardNeg(x.toRat) = x for finite non-zero x (negative case). -/
private theorem round_rtn_nonzero_neg (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = true) :
    roundTowardNeg (x.toRat) = x := by
  have hexp_lt := finite_implies_exp_lt x hfin
  have hsign := toRat_lt_zero_iff x hfin hne
  have hfbe := findBiasedExp_correct x hfin hne
  have hneg : x.toRat < 0 := hsign.mpr hs
  have hrs := roundSignificand_rtp_up_exact x hfin hne
  unfold roundTowardNeg
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

/-- roundTowardNeg(x.toRat) = x for finite non-zero x. -/
theorem round_rtn_nonzero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    roundTowardNeg (x.toRat) = x := by
  cases hs : x.sign
  · exact round_rtn_nonzero_pos x hfin hne hs
  · exact round_rtn_nonzero_neg x hfin hne hs

/-- roundTowardNeg is idempotent on all finite F64 values:
    roundTowardNeg(toRat(x)) = x  (up to signed zero collapsing). -/
theorem round_rtn_idempotent (x : F64) (hfin : x.isFinite) :
    roundTowardNeg (x.toRat) = x ∨
    (x.toRat = 0 ∧ roundTowardNeg (x.toRat) = posZero) := by
  by_cases hne : x.toRat = 0
  · right; exact ⟨hne, by rw [hne]; exact round_rtn_zero⟩
  · left; exact round_rtn_nonzero x hfin hne

end F64
