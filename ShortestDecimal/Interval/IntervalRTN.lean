/-
  Interval/IntervalRTN.lean

  The acceptance interval for round-toward-negative-infinity (RTN).
  Positive case reuses RTZ. Negative case requires ceiling proof.
-/
import ShortestDecimal.IEEE754.RoundProofRTN
import ShortestDecimal.Interval.Interval
import ShortestDecimal.Interval.IntervalRTZ
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace ShortestDecimal

/-- The RTN acceptance interval. -/
def rtnInterval (x : F64) (hfin : x.isFinite) : AcceptanceInterval :=
  if x.sign then
    let mf := x.effectiveSignificand
    let e2 := x.effectiveBinaryExp - 2
    let delta : Nat := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4
    let scaleN (n : Nat) : ℚ :=
      if e2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ e2.toNat
      else (n : ℚ) / (2 : ℚ) ^ (-e2).toNat
    { low := -(scaleN (4 * mf)), high := -(scaleN (4 * mf - delta)),
      lowInclusive := true, highInclusive := false }
  else
    rtzInterval x hfin

/-- For positive q, roundTowardNeg(q) = roundTowardZero(q). -/
theorem roundTowardNeg_eq_rtz_of_pos (q : ℚ) (hne : q ≠ 0) (hpos : ¬(q < 0)) :
    F64.roundTowardNeg q = F64.roundTowardZero q := by
  have hdec : decide (q < 0) = false := decide_eq_false hpos
  simp only [F64.roundTowardNeg, F64.roundTowardZero, hne, hpos, hdec, ite_false, ite_true,
             decide_false, decide_true]
  rfl

/-! ## Main soundness -/

set_option maxHeartbeats 800000 in
theorem rtn_interval_correct (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0)
    (q : ℚ) (hq : (rtnInterval x hfin).contains q) :
    F64.roundTowardNeg q = x := by
  unfold rtnInterval at hq
  cases hs : x.sign
  · -- Positive x: interval = RTZ interval
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
    have hq_pos : ¬(q < 0) := by
      have ⟨habs_lo_pos, _⟩ := rtz_abs_interval_pos x hfin hne
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at habs_lo_pos
      -- habs_lo_pos : 0 < (rtzInterval x hfin).low
      unfold AcceptanceInterval.contains at hq
      obtain ⟨hlo, _⟩ := hq
      split at hlo <;> linarith
    have hq_ne : q ≠ 0 := by
      intro heq; subst heq
      have ⟨habs_lo_pos, _⟩ := rtz_abs_interval_pos x hfin hne
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at habs_lo_pos
      unfold AcceptanceInterval.contains at hq
      obtain ⟨hlo, _⟩ := hq
      split at hlo <;> linarith
    rw [roundTowardNeg_eq_rtz_of_pos q hq_ne hq_pos]
    exact rtz_interval_correct x hfin hne q hq
  · -- Negative x: ceiling-based proof (mirror of RTP positive)
    simp only [hs, ite_true] at hq
    sorry

end ShortestDecimal
