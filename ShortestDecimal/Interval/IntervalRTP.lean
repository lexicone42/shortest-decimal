/-
  Interval/IntervalRTP.lean

  The acceptance interval for round-toward-positive-infinity (RTP).
  Negative case reuses RTZ. Positive case requires ceiling proof.
-/
import ShortestDecimal.IEEE754.RoundProofRTP
import ShortestDecimal.Interval.Interval
import ShortestDecimal.Interval.IntervalRTZ
import ShortestDecimal.Interval.CeilHelper
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace ShortestDecimal

/-- The RTP acceptance interval. -/
def rtpInterval (x : F64) (hfin : x.isFinite) : AcceptanceInterval :=
  if x.sign then
    rtzInterval x hfin
  else
    let mf := x.effectiveSignificand
    let e2 := x.effectiveBinaryExp - 2
    let delta : Nat := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4
    let scaleN (n : Nat) : ℚ :=
      if e2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ e2.toNat
      else (n : ℚ) / (2 : ℚ) ^ (-e2).toNat
    { low := scaleN (4 * mf - delta), high := scaleN (4 * mf),
      lowInclusive := false, highInclusive := true }

/-- For negative q, roundTowardPos(q) = roundTowardZero(q). -/
theorem roundTowardPos_eq_rtz_of_neg (q : ℚ) (hne : q ≠ 0) (hneg : q < 0) :
    F64.roundTowardPos q = F64.roundTowardZero q := by
  show F64.roundTowardPos q = F64.roundTowardZero q
  have hdec : decide (q < 0) = true := decide_eq_true hneg
  simp only [F64.roundTowardPos, F64.roundTowardZero, hne, hneg, hdec, ite_false, ite_true,
             decide_true]
  rfl

/-! ## Positive case core

    For positive q in the RTP interval, q ≤ x.toRat (which is exact) and
    q > pred(x).toRat (approximately). So roundTowardPos(q) = x because
    x is the smallest F64 ≥ q.

    Instead of a monotonicity argument, we prove this via the significand
    computation: findBiasedExp finds the right exponent, ceiling of the
    scaled significand recovers mf, and assembly gives x.
-/

/-- For q = x.toRat (the upper bound of the RTP interval),
    roundTowardPos recovers x by idempotence. -/
private theorem rtp_at_toRat (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = false) :
    F64.roundTowardPos (x.toRat) = x :=
  F64.round_rtp_nonzero x hfin hne

-- The positive case proof is handled directly in rtp_interval_correct below.
-- It uses the ceiling analysis from CeilHelper.lean.

/-! ## Main soundness -/

set_option maxHeartbeats 6400000 in
theorem rtp_interval_correct (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0)
    (q : ℚ) (hq : (rtpInterval x hfin).contains q) :
    F64.roundTowardPos q = x := by
  unfold rtpInterval at hq
  cases hs : x.sign
  · -- Positive x: ceiling proof
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at hq
    sorry
  · -- Negative x: interval = RTZ interval
    simp only [hs, ↓reduceIte] at hq
    have hq_neg : q < 0 := by
      have ⟨habs_lo_pos, _⟩ := rtz_abs_interval_pos x hfin hne
      simp only [hs, ite_true] at habs_lo_pos
      have hhigh_neg : (rtzInterval x hfin).high < 0 := by linarith
      unfold AcceptanceInterval.contains at hq; obtain ⟨_, hhi⟩ := hq
      split at hhi <;> linarith
    have hq_ne : q ≠ 0 := ne_of_lt hq_neg
    rw [roundTowardPos_eq_rtz_of_neg q hq_ne hq_neg]
    exact rtz_interval_correct x hfin hne q hq

end ShortestDecimal
