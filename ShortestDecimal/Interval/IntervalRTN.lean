/-
  Interval/IntervalRTN.lean

  The acceptance interval for round-toward-negative-infinity (RTN).
  Positive case reuses RTZ. Negative case requires ceiling proof.
-/
import ShortestDecimal.IEEE754.RoundProofRTN
import ShortestDecimal.Interval.Interval
import ShortestDecimal.Interval.IntervalRTZ
import ShortestDecimal.Interval.IntervalRTP
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

/-- The RTN acceptance interval. Uses scaleQ directly (not a local let)
    to ensure hypotheses after unfold match scaleQ terms in proofs. -/
def rtnInterval (x : F64) (hfin : x.isFinite) : AcceptanceInterval :=
  if x.sign then
    let mf := x.effectiveSignificand
    let e2 := x.effectiveBinaryExp - 2
    let delta : Nat := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4
    { low := -(scaleQ (4 * mf) e2), high := -(scaleQ (4 * mf - delta) e2),
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

/-! ## Negative case: mirror of RTP positive

    For negative x with sign=true, the RTN interval is
    [-scaleN(4*mf), -scaleN(4*mf-delta)) with lowInclusive=true, highInclusive=false.

    For q in this interval: |q| ∈ (scaleN(4*mf-delta), scaleN(4*mf)]
    This is the same interval structure as RTP positive.
    roundTowardNeg for negative q uses roundSignificand_rtp_up on |q|.
-/

/-- Extract |q| bounds from the negative-x RTN interval. -/
private theorem rtn_neg_abs_bounds (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (hs : x.sign = true) (q : ℚ)
    (hq : (rtnInterval x hfin).contains q) :
    let delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat)
    q < 0 ∧
    scaleQ (4 * x.effectiveSignificand - delta) (x.effectiveBinaryExp - 2) < |q| ∧
    |q| ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2) := by
  simp only []
  unfold rtnInterval at hq; simp only [hs, ite_true] at hq
  unfold AcceptanceInterval.contains at hq
  simp only [Bool.true_eq_false, ↓reduceIte] at hq
  obtain ⟨hlo, hhi⟩ := hq
  -- Now hlo and hhi are in terms of scaleQ (not inlined scaleN)
  have hmf_pos := rtp_effSig_pos x hfin hne
  set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat)
  have hscale4_pos := scaleQ_pos (4 * x.effectiveSignificand) (by omega) (x.effectiveBinaryExp - 2)
  -- Simplify the if-then-else in hhi (highInclusive = false)
  simp only [Bool.false_eq_true, ↓reduceIte] at hhi
  -- Now hhi : q < -(scaleQ (4*mf - delta) e2)
  -- hlo : -(scaleQ (4*mf) e2) ≤ q
  -- Since scaleQ(4*mf) > 0, -(scaleQ(4*mf)) < 0, and q ≥ -(scaleQ(4*mf)), and q < -(scaleQ(4*mf-delta)) ≤ 0
  have hq_neg : q < 0 := by
    have : scaleQ (4 * x.effectiveSignificand - delta) (x.effectiveBinaryExp - 2) ≥ 0 := by
      unfold scaleQ; split <;> positivity
    linarith
  refine ⟨hq_neg, ?_, ?_⟩
  · rw [abs_of_neg hq_neg]; linarith
  · rw [abs_of_neg hq_neg]; linarith

/-- The core of the RTN negative case: use the same machinery as RTP positive. -/
private theorem rtn_neg_core (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0) (hq_neg : q < 0)
    (hs : x.sign = true)
    (habs_lo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < |q|)
    (habs_hi : |q| ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2)) :
    F64.roundTowardNeg q = x := by
  -- The proof mirrors rtp_round_same_exp / rtp_round_boundary but for negative q
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have habs_pos : 0 < |q| := abs_pos.mpr hq_ne
  have hneg : q < 0 := hq_neg
  -- roundTowardNeg for negative q uses roundSignificand_rtp_up on |q|
  -- Same findBiasedExp and significand analysis as RTP
  set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) with hdelta_def
  -- Step 1: Determine findBiasedExp |q|
  -- The |q| bounds are the same as in the RTP positive case
  -- We can reuse the same argument
  by_cases hfbe : F64.findBiasedExp |q| = x.biasedExp.val
  · -- Same-exponent case
    have hmf_pos := rtp_effSig_pos x hfin hne
    have hdelta_le : delta ≤ 4 := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) ≤ 4; split <;> omega
    have hdelta_le_4mf : delta ≤ 4 * x.effectiveSignificand := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) ≤ 4 * x.effectiveSignificand
      split <;> omega
    have hsig_lo := rtp_sigExact_lower_strict (4 * x.effectiveSignificand - delta) |q| x.effectiveBinaryExp habs_lo
    have hsig_hi := rtp_sigExact_upper (4 * x.effectiveSignificand) |q| x.effectiveBinaryExp habs_hi
    have hlo_mf : (x.effectiveSignificand : ℚ) - 1 ≤ ((4 * x.effectiveSignificand - delta : ℕ) : ℚ) / 4 := by
      push_cast [Nat.cast_sub hdelta_le_4mf]
      linarith [show (delta : ℚ) ≤ 4 from by exact_mod_cast hdelta_le]
    have hhi_mf : ((4 * x.effectiveSignificand : ℕ) : ℚ) / 4 = (x.effectiveSignificand : ℚ) := by
      push_cast; ring
    have hrs : F64.roundSignificand_rtp_up |q| x.biasedExp.val = (x.mantissa.val, false) := by
      rw [roundSignificand_rtp_up_split]
      have hsig := sigCeilOf_from_bounds x hfin hne |q|
        (lt_of_le_of_lt hlo_mf hsig_lo) (by rw [← hhi_mf]; exact hsig_hi)
      rw [hsig]; exact branchOfCeil_mf x
    -- Assembly
    unfold F64.roundTowardNeg
    rw [if_neg hq_ne]
    simp only [if_pos hneg]
    rw [hfbe, hrs]
    simp only [show (false = true) = False from by decide, ite_false]
    rw [if_neg (by unfold F64.maxBiasedExp; omega)]
    unfold F64.mkFinite
    simp only [show x.biasedExp.val < 2047 from hexp_lt,
               show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
    have hdec : decide (q < 0) = true := decide_eq_true hneg
    rw [hdec]
    rcases x with ⟨s, be, m⟩; simp only at hs; rw [hs]
  · -- Boundary case: findBiasedExp |q| = biasedExp - 1
    -- Same argument as rtp_round_boundary but for negative sign
    have hbexp := rtp_boundary_bexp_ge_one x hfin hne |q| habs_pos habs_hi hfbe
    have hmant := rtp_boundary_mant_zero x hfin hne |q| habs_pos habs_lo habs_hi hfbe
    have hfbe_eq := rtp_boundary_fbe_eq x hfin hne |q| habs_pos habs_lo habs_hi hfbe
    have hrs := rtp_boundary_roundSig x hfin hne |q| habs_pos habs_lo habs_hi hfbe
    -- Assembly with bump
    unfold F64.roundTowardNeg
    rw [if_neg hq_ne]
    simp only [if_pos hneg]
    rw [hfbe_eq, hrs]
    simp only [ite_true]
    have hfinalExp : x.biasedExp.val - 1 + 1 = x.biasedExp.val := by omega
    rw [hfinalExp]
    have hlt_max : ¬(x.biasedExp.val ≥ F64.maxBiasedExp) := by unfold F64.maxBiasedExp; omega
    rw [if_neg hlt_max]
    unfold F64.mkFinite
    simp only [show x.biasedExp.val < 2047 from hexp_lt,
               show (0:Nat) < 2^52 from by norm_num, dite_true]
    have hdec : decide (q < 0) = true := decide_eq_true hneg
    rw [hdec]
    rcases x with ⟨s, ⟨be, hbe_bound⟩, ⟨m, hm_bound⟩⟩
    rw [F64.mk.injEq]
    refine ⟨by simp at hs; exact hs.symm, Fin.ext rfl, Fin.ext ?_⟩
    simp at hmant; exact hmant.symm

/-! ## Main soundness -/

set_option maxHeartbeats 6400000 in
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
    -- Reconstruct the interval containment for the full definition
    have hq_full : (rtnInterval x hfin).contains q := by
      unfold rtnInterval; simp only [hs, ite_true]; exact hq
    have ⟨hq_neg, habs_lo, habs_hi⟩ := rtn_neg_abs_bounds x hfin hne hs q hq_full
    have hq_ne : q ≠ 0 := ne_of_lt hq_neg
    exact rtn_neg_core x hfin hne q hq_ne hq_neg hs habs_lo habs_hi

end ShortestDecimal
