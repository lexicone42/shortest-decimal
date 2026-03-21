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

/-! ## Positive case core -/

theorem rtp_effSig_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    x.effectiveSignificand ≥ 1 := by
  by_contra h; push_neg at h
  have : x.effectiveSignificand = 0 := by omega
  exact hne (by unfold F64.toRat; rw [if_neg (not_not.mpr hfin)]; simp [this])

/-! ### Scaling lemmas for ceiling direction -/

private theorem pow_ef_cancel' (ef : Int) (hef2 : ¬(ef - 2 ≥ 0)) (hef : ef ≥ 0) :
    (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = 4 := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem pow_ef_cancel_neg' (ef : Int) (hef : ef < 0) :
    (2:ℚ) ^ (-ef).toNat * 4 = 2 ^ (-(ef - 2)).toNat := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

/-- Strict lower bound: scaleQ(n, ef-2) < qAbs → n/4 < sigExact -/
theorem rtp_sigExact_lower_strict (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : scaleQ n (ef - 2) < qAbs) :
    (n : ℚ) / 4 <
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  unfold scaleQ at hscale
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add]; congr 2; omega]
  · push_neg at hef2
    by_cases hef : ef ≥ 0
    · simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, if_pos hef] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_right hlt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel' ef (by omega) hef]]
    · push_neg at hef
      simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, show ¬(ef ≥ 0) from by omega] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg' ef (by omega)]]

/-- Non-strict upper bound: qAbs ≤ scaleQ(n, ef-2) → sigExact ≤ n/4 -/
theorem rtp_sigExact_upper (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs ≤ scaleQ n (ef - 2)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) ≤ (n : ℚ) / 4 := by
  unfold scaleQ at hscale
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add]; congr 2; omega]
  · push_neg at hef2
    by_cases hef : ef ≥ 0
    · simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, if_pos hef] at hscale ⊢
      have hle := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_right hle (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel' ef (by omega) hef]]
    · push_neg at hef
      simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, show ¬(ef ≥ 0) from by omega] at hscale ⊢
      have hle := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [le_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg' ef (by omega)]]

/-! ### Same-exponent case -/

theorem rtp_round_same_exp (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0) (hq_pos : 0 < q)
    (hs : x.sign = false)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe : F64.findBiasedExp q = x.biasedExp.val) :
    F64.roundTowardPos q = x := by
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have habs_eq : |q| = q := abs_of_pos hq_pos
  have hpos : ¬(q < 0) := not_lt.mpr (le_of_lt hq_pos)
  unfold F64.roundTowardPos
  rw [if_neg hq_ne]
  simp only [if_neg hpos]
  rw [habs_eq, hfbe]
  have hrs : F64.roundSignificand_rtp_up q x.biasedExp.val = (x.mantissa.val, false) := by
    rw [roundSignificand_rtp_up_split]
    set mf := x.effectiveSignificand
    set ef := x.effectiveBinaryExp
    set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) with hdelta_def
    have hmf_pos := rtp_effSig_pos x hfin hne
    have hdelta_le : delta ≤ 4 := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) ≤ 4; split <;> omega
    have hdelta_le_4mf : delta ≤ 4 * mf := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) ≤ 4 * mf; split <;> omega
    have hsig_lo := rtp_sigExact_lower_strict (4 * mf - delta) q ef hlo
    have hsig_hi := rtp_sigExact_upper (4 * mf) q ef hhi
    have hlo_mf : (mf : ℚ) - 1 ≤ ((4 * mf - delta : ℕ) : ℚ) / 4 := by
      push_cast [Nat.cast_sub hdelta_le_4mf]
      linarith [show (delta : ℚ) ≤ 4 from by exact_mod_cast hdelta_le]
    have hhi_mf : ((4 * mf : ℕ) : ℚ) / 4 = (mf : ℚ) := by push_cast; ring
    have hsig := sigCeilOf_from_bounds x hfin hne q
      (lt_of_le_of_lt hlo_mf hsig_lo) (by rw [← hhi_mf]; exact hsig_hi)
    rw [hsig]
    exact branchOfCeil_mf x
  rw [hrs]
  simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold F64.maxBiasedExp; omega)]
  unfold F64.mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt,
             show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
  have hdec : decide (q < 0) = false := decide_eq_false hpos
  rw [hdec]
  rcases x with ⟨s, be, m⟩; simp only at hs; rw [hs]

/-! ### Boundary case -/

theorem rtp_boundary_bexp_ge_one (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    x.biasedExp.val ≥ 1 := by
  by_contra hlt; push_neg at hlt
  have hbexp0 : x.biasedExp.val = 0 := by omega
  have hesig_lt : x.effectiveSignificand < 2^52 := by
    unfold F64.effectiveSignificand; simp [hbexp0]
  have he2 : x.effectiveBinaryExp - 2 = -1076 := by
    unfold F64.effectiveBinaryExp F64.expBias F64.mantBits; simp [hbexp0]
  rw [he2] at hhi
  have hq_lt_thresh : q < F64.threshQ 1 :=
    calc q ≤ scaleQ (4 * x.effectiveSignificand) (-1076) := hhi
      _ < scaleQ (4 * x.effectiveSignificand + 4) (-1076) :=
          scaleQ_lt _ _ (by omega) _
      _ ≤ F64.threshQ 1 := subnormal_le_threshQ1 x.effectiveSignificand hesig_lt
  have habs_eq : |q| = q := abs_of_pos hq_pos
  have hfbe_zero : F64.findBiasedExp q = 0 := by
    rw [← habs_eq]
    unfold F64.findBiasedExp; apply F64.go_eq
    · omega
    · left; rfl
    · intro e he hle; push_neg; rw [habs_eq]
      calc q < F64.threshQ 1 := hq_lt_thresh
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  rw [hfbe_zero, hbexp0] at hfbe_ne
  exact absurd rfl hfbe_ne

theorem rtp_boundary_mant_zero (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    x.mantissa.val = 0 := by
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  by_contra hmant_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig := F64.esig_normal x (by omega : x.biasedExp.val ≠ 0)
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) = 4 := by
    simp [hmant_ne]
  rw [hdelta] at hlo; rw [he2] at hlo hhi
  have hesig_ge : x.effectiveSignificand ≥ 2^52 + 1 := by rw [hesig]; omega
  have hesig_lt_nat : x.effectiveSignificand < 2^53 := by
    have h := F64.effectiveSignificand_lt x hfin; omega
  -- 4*(mf-1) = 4*mf-4, and mf-1 ≥ 2^52
  have hmf_sub : 4 * (x.effectiveSignificand - 1) = 4 * x.effectiveSignificand - 4 := by omega
  have hge_thresh : F64.threshQ x.biasedExp.val ≤ q := by
    calc F64.threshQ x.biasedExp.val
        ≤ scaleQ (4 * (x.effectiveSignificand - 1)) ((x.biasedExp.val : Int) - 1077) :=
          scaleQ_ge_threshQ (x.effectiveSignificand - 1) _ (by omega) hbexp hexp_lt
      _ ≤ scaleQ (4 * x.effectiveSignificand - 4) ((x.biasedExp.val : Int) - 1077) :=
          scaleQ_le _ _ (by omega) _
      _ ≤ q := le_of_lt hlo
  have hlt_thresh : q < F64.threshQ (x.biasedExp.val + 1) := by
    calc q ≤ scaleQ (4 * x.effectiveSignificand) ((x.biasedExp.val : Int) - 1077) := hhi
      _ < scaleQ (4 * x.effectiveSignificand + 4) ((x.biasedExp.val : Int) - 1077) :=
          scaleQ_lt _ _ (by omega) _
      _ ≤ F64.threshQ (x.biasedExp.val + 1) :=
          scaleQ_le_threshQ_succ _ _ hesig_lt_nat hbexp hexp_lt
  have habs_eq : |q| = q := abs_of_pos hq_pos
  have hfbe : F64.findBiasedExp q = x.biasedExp.val := by
    rw [← habs_eq]
    unfold F64.findBiasedExp; apply F64.go_eq
    · omega
    · right; rw [habs_eq]; exact hge_thresh
    · intro e hgt hle; push_neg; rw [habs_eq]
      calc q < F64.threshQ (x.biasedExp.val + 1) := hlt_thresh
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  exact absurd hfbe hfbe_ne

theorem rtp_boundary_qabs_lt_thresh (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    q < F64.threshQ x.biasedExp.val := by
  by_contra hge; push_neg at hge
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  have hmant := rtp_boundary_mant_zero x hfin hne q hq_pos hlo hhi hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  rw [hesig_val, he2] at hhi
  have hlt_thresh : q < F64.threshQ (x.biasedExp.val + 1) := by
    calc q ≤ scaleQ (4 * 2^52) ((x.biasedExp.val : Int) - 1077) := hhi
      _ < scaleQ (4 * 2^52 + 4) ((x.biasedExp.val : Int) - 1077) :=
          scaleQ_lt _ _ (by norm_num) _
      _ ≤ F64.threshQ (x.biasedExp.val + 1) :=
          scaleQ_le_threshQ_succ (2^52) _ (by norm_num) hbexp hexp_lt
  have habs_eq : |q| = q := abs_of_pos hq_pos
  have hfbe : F64.findBiasedExp q = x.biasedExp.val := by
    rw [← habs_eq]
    unfold F64.findBiasedExp; apply F64.go_eq
    · omega
    · right; rw [habs_eq]; exact hge
    · intro e hgt hle; push_neg; rw [habs_eq]
      calc q < F64.threshQ (x.biasedExp.val + 1) := hlt_thresh
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  exact absurd hfbe hfbe_ne

theorem rtp_boundary_qabs_ge_prev (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2)) :
    F64.threshQ (x.biasedExp.val - 1) ≤ q := by
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  have hmant := rtp_boundary_mant_zero x hfin hne q hq_pos hlo hhi hfbe_ne
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) =
      if x.biasedExp.val > 1 then 2 else 4 := by simp [hmant]
  rw [hdelta, hesig_val, he2] at hlo
  -- hlo : scaleQ (4 * 2^52 - if be > 1 then 2 else 4) (be - 1077) < q
  -- We need: threshQ(be - 1) ≤ q
  -- Strategy: threshQ(be-1) < lo_bound ≤ scaleQ(...) ≤ q
  by_cases hbe1 : x.biasedExp.val = 1
  · -- be = 1: delta = 4, lo_bound = 4*2^52 - 4
    have hbe_sub : x.biasedExp.val - 1 = 0 := by omega
    rw [hbe1] at hlo; rw [hbe_sub]
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte] at hlo
    -- hlo: scaleQ(4*2^52 - 4, (1:Nat:Int) - 1077) < q
    -- threshQ(0) < scaleQ(4*2^52-4, -1076) because (2^54-4)/2^1076 > 1/2^1023
    have hkey : F64.threshQ 0 < scaleQ (4 * 2^52 - 4) ((1:Int) - 1077) := by
      unfold F64.threshQ scaleQ
      simp only [show ¬(0 ≥ 1023) from by omega, ↓reduceIte,
                 show 1023 - 0 = 1023 from by omega,
                 show ¬((1:Int) - 1077 ≥ 0) from by omega,
                 show (-(((1:Int) - 1077))).toNat = 1076 from by omega]
      rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
      norm_num
    exact le_of_lt (lt_trans hkey hlo)
  · -- be ≥ 2: delta = 2, lo_bound = 4*2^52 - 2
    have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    -- threshQ(be-1) < scaleQ(4*2^52-2, be-1077) ≤ lo_bound < q
    have hsuff : F64.threshQ (x.biasedExp.val - 1) < scaleQ (4 * 2^52 - 2) ((x.biasedExp.val : Int) - 1077) := by
      by_cases hge1077 : (x.biasedExp.val : Int) - 1077 ≥ 0
      · unfold scaleQ; simp only [show (x.biasedExp.val : Int) - 1077 ≥ 0 from hge1077, ↓reduceIte]
        have htonat : ((x.biasedExp.val : Int) - 1077).toNat = x.biasedExp.val - 1077 := by omega
        rw [htonat]
        unfold F64.threshQ; simp only [show x.biasedExp.val - 1 ≥ 1023 from by omega, ↓reduceIte]
        calc (2:ℚ) ^ (x.biasedExp.val - 1 - 1023)
            = 2^53 * 2^(x.biasedExp.val - 1077) := by rw [← pow_add]; congr 1; omega
          _ < ((4 * 2^52 - 2 : Nat) : ℚ) * 2^(x.biasedExp.val - 1077) :=
              mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      · push_neg at hge1077
        unfold scaleQ; simp only [show ¬((x.biasedExp.val : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
        have htonat : (-((x.biasedExp.val : Int) - 1077)).toNat = 1077 - x.biasedExp.val := by omega
        rw [htonat]
        unfold F64.threshQ
        by_cases hge1024 : x.biasedExp.val - 1 ≥ 1023
        · simp only [show x.biasedExp.val - 1 ≥ 1023 from hge1024, ↓reduceIte]
          rw [lt_div_iff₀ (by positivity : (0:ℚ) < 2^(1077 - x.biasedExp.val))]
          calc (2:ℚ) ^ (x.biasedExp.val - 1 - 1023) * 2^(1077 - x.biasedExp.val)
              = 2^53 := by rw [← pow_add]; congr 1; omega
            _ < ((4 * 2^52 - 2 : Nat) : ℚ) := by norm_num
        · push_neg at hge1024
          simp only [show ¬(x.biasedExp.val - 1 ≥ 1023) from by omega, ↓reduceIte]
          rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
          calc (2:ℚ) ^ (1077 - x.biasedExp.val)
              = 2^53 * 2^(1023 - (x.biasedExp.val - 1)) := by rw [← pow_add]; congr 1; omega
            _ < ((4 * 2^52 - 2 : Nat) : ℚ) * 2^(1023 - (x.biasedExp.val - 1)) :=
                mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    -- Now chain: threshQ(be-1) < scaleQ(4*2^52-2, be-1077) ≤ lo_bound < q
    -- Since be > 1, the if evaluates to 2, so 4*2^52 - 2 = 4*2^52 - (if be>1 then 2 else 4)
    have heq : (4 * 2^52 - 2 : Nat) = 4 * 2^52 - (if x.biasedExp.val > 1 then 2 else 4 : Nat) := by
      simp [show x.biasedExp.val > 1 from by omega]
    exact le_of_lt (lt_trans hsuff (heq ▸ hlo))

theorem rtp_boundary_fbe_eq (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    F64.findBiasedExp q = x.biasedExp.val - 1 := by
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  have hqlt := rtp_boundary_qabs_lt_thresh x hfin hne q hq_pos hlo hhi hfbe_ne
  have hqge := rtp_boundary_qabs_ge_prev x hfin hne q hq_pos hlo hfbe_ne hhi
  have habs_eq : |q| = q := abs_of_pos hq_pos
  rw [← habs_eq]
  unfold F64.findBiasedExp
  apply F64.go_eq
  · omega
  · by_cases hbe1 : x.biasedExp.val = 1
    · left; omega
    · right; rw [habs_eq]; exact hqge
  · intro e he hle; push_neg; rw [habs_eq]
    calc q < F64.threshQ x.biasedExp.val := hqlt
      _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)

/-! #### Boundary: sigExact conversion -/

theorem rtp_boundary_sigExact_lo_sub (qAbs : ℚ)
    (habs_lo : ((4 * 2 ^ 52 - 4 : Nat) : ℚ) / 2 ^ 1076 < qAbs) :
    (2^52 : ℚ) - 1 < qAbs * 2^1074 := by
  have hscale : ((4 * 2^52 - 4 : Nat) : ℚ) / 2^1076 * 2^1074 = 2^52 - 1 := by
    have h1 : (2:ℚ)^1076 = 2^2 * 2^1074 := by rw [← pow_add]
    rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^1074 ≠ 0)]
    push_cast; norm_num
  linarith [mul_lt_mul_of_pos_right habs_lo (show (0:ℚ) < 2^1074 from by positivity)]

theorem rtp_boundary_sigExact_hi_sub (qAbs : ℚ)
    (hqlt : qAbs < (1:ℚ) / 2^1022) :
    qAbs * 2^1074 < 2^52 := by
  have hscale : (1:ℚ) / 2^1022 * 2^1074 = 2^52 := by
    rw [one_div, inv_mul_eq_div]
    rw [show (2:ℚ)^1074 = 2^52 * 2^1022 from by rw [← pow_add]]
    rw [mul_div_cancel_right₀ _ (by positivity : (2:ℚ)^1022 ≠ 0)]
  linarith [mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^1074 from by positivity)]

theorem rtp_boundary_sigExact_lo_norm (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (habs_lo : (if (bexp : Int) - 1077 ≥ 0
      then ((2^54 - 2 : Nat) : ℚ) * 2^((bexp : Int) - 1077).toNat
      else ((2^54 - 2 : Nat) : ℚ) / 2^(-((bexp : Int) - 1077)).toNat) < qAbs) :
    (2^53 : ℚ) - 1 <
      (if ((bexp : Int) - 1076 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 1076).toNat : ℚ)
       else qAbs * (2 ^ (-((bexp : Int) - 1076)).toNat : ℚ)) := by
  by_cases hbinexp_ge : (bexp : Int) - 1076 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 1076).toNat = bexp - 1076 := by omega
    rw [htonat]
    by_cases hge1077 : (bexp : Int) - 1077 ≥ 0
    · simp only [if_pos hge1077] at habs_lo
      have htonat2 : ((bexp : Int) - 1077).toNat = bexp - 1077 := by omega
      rw [htonat2] at habs_lo
      rw [lt_div_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 1076))]
      calc ((2:ℚ)^53 - 1) * 2^(bexp - 1076)
          = ((2^54 - 2 : Nat) : ℚ) * 2^(bexp - 1077) := by
            push_cast
            rw [show (2:ℚ)^(bexp - 1076) = 2^1 * 2^(bexp - 1077) from by
              rw [← pow_add]; congr 1; omega]
            ring
        _ < qAbs := habs_lo
    · push_neg at hge1077
      have hbe_eq : bexp = 1076 := by omega
      simp only [show ¬((bexp : Int) - 1077 ≥ 0) from by omega, ↓reduceIte] at habs_lo
      have htonat2 : (-((bexp : Int) - 1077)).toNat = 1077 - bexp := by omega
      rw [htonat2, hbe_eq] at habs_lo
      rw [hbe_eq, show 1076 - 1076 = 0 from by omega, pow_zero, div_one]
      have : ((2^54 - 2 : Nat) : ℚ) / 2 ^ 1 = 2^53 - 1 := by push_cast; norm_num
      linarith
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 1076 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 1076)).toNat = 1076 - bexp := by omega
    rw [htonat]
    have he2_neg : ¬((bexp : Int) - 1077 ≥ 0) := by omega
    simp only [he2_neg, ↓reduceIte] at habs_lo
    have htonat3 : (-((bexp : Int) - 1077)).toNat = 1077 - bexp := by omega
    rw [htonat3] at habs_lo
    have h := mul_lt_mul_of_pos_right habs_lo (show (0:ℚ) < 2^(1076 - bexp) from by positivity)
    calc (2^53 : ℚ) - 1
        = ((2^54 - 2 : Nat) : ℚ) / 2^(1077 - bexp) * 2^(1076 - bexp) := by
          push_cast
          have h1 : (2:ℚ)^(1077 - bexp) = 2^1 * 2^(1076 - bexp) := by
            rw [← pow_add]; congr 1; omega
          rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^(1076 - bexp) ≠ 0)]
          norm_num
      _ < qAbs * 2^(1076 - bexp) := h

theorem rtp_boundary_sigExact_hi_norm (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (hexp_lt : bexp < 2047)
    (hqlt : qAbs < F64.threshQ bexp) :
    (if ((bexp : Int) - 1076 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 1076).toNat : ℚ)
     else qAbs * (2 ^ (-((bexp : Int) - 1076)).toNat : ℚ)) < 2^53 := by
  by_cases hbinexp_ge : (bexp : Int) - 1076 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 1076).toNat = bexp - 1076 := by omega
    rw [htonat]
    unfold F64.threshQ at hqlt
    simp only [show bexp ≥ 1023 from by omega, ↓reduceIte] at hqlt
    rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 1076))]
    calc qAbs < 2^(bexp - 1023) := hqlt
      _ = 2^53 * 2^(bexp - 1076) := by rw [← pow_add]; congr 1; omega
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 1076 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 1076)).toNat = 1076 - bexp := by omega
    rw [htonat]
    unfold F64.threshQ at hqlt
    by_cases hge1023 : bexp ≥ 1023
    · simp only [show bexp ≥ 1023 from hge1023, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(1076 - bexp) from by positivity)
      calc qAbs * 2^(1076 - bexp)
          < 2^(bexp - 1023) * 2^(1076 - bexp) := h
        _ = 2^53 := by rw [← pow_add]; congr 1; omega
    · push_neg at hge1023
      simp only [show ¬(bexp ≥ 1023) from by omega, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(1076 - bexp) from by positivity)
      calc qAbs * 2^(1076 - bexp)
          < 1 / 2^(1023 - bexp) * 2^(1076 - bexp) := h
        _ = 2^53 := by
            rw [one_div, inv_mul_eq_div]
            rw [div_eq_iff (by positivity : (0:ℚ) < 2^(1023 - bexp)).ne']
            rw [← pow_add]; congr 1; omega

theorem rtp_boundary_roundSig (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_pos : 0 < q)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    F64.roundSignificand_rtp_up q (x.biasedExp.val - 1) = (0, true) := by
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  have hmant := rtp_boundary_mant_zero x hfin hne q hq_pos hlo hhi hfbe_ne
  have hqlt := rtp_boundary_qabs_lt_thresh x hfin hne q hq_pos hlo hhi hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^52 := by
    rw [F64.esig_normal x (by omega)]; simp [hmant]
  have hebe := F64.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) =
      if x.biasedExp.val > 1 then 2 else 4 := by simp [hmant]
  rw [hdelta, hesig_val, he2] at hlo
  rw [hesig_val, he2] at hhi
  rw [roundSignificand_rtp_up_split]
  by_cases hbe1 : x.biasedExp.val = 1
  · simp only [hbe1, show 1 - 1 = 0 from by omega]
    suffices hsig : sigCeilOf q 0 = 2^52 by
      rw [hsig]; unfold branchOfCeil; simp
    rw [hbe1] at hlo hhi hqlt
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte,
               show (4 * (2:Nat)^52 - 4) = (2^54 - 4 : Nat) from by norm_num,
               show ((1:Nat) : Int) - 1077 = -1076 from by omega] at hlo
    simp only [show ((1:Nat) : Int) - 1077 = -1076 from by omega] at hhi
    unfold F64.threshQ at hqlt; simp only [show ¬(1 ≥ 1023) from by omega, ↓reduceIte,
                                           show 1023 - 1 = 1022 from by omega] at hqlt
    -- Need: sigExact ∈ (2^52 - 1, 2^52] where sigExact = q * 2^1074
    -- scaleQ(2^54-4, -1076) < q: (2^54-4)/2^1076 < q, so (2^52-1) < q*2^1074
    -- q < threshQ 1 = 1/2^1022: q*2^1074 ≤ 2^52
    have hN : (2:Nat)^52 ≥ 1 := by norm_num
    exact sigCeilOf_eq_of_bounds q 0 (2^52) hN
      (by simp only [↓reduceIte, show ¬((-1074 : Int) ≥ 0) from by omega,
                      show ((-(-1074 : Int)).toNat) = 1074 from by omega]
          exact rtp_boundary_sigExact_lo_sub q hlo)
      (by simp only [↓reduceIte, show ¬((-1074 : Int) ≥ 0) from by omega,
                      show ((-(-1074 : Int)).toNat) = 1074 from by omega]
          exact rtp_boundary_sigExact_hi_sub q hqlt)
  · have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    have hbm1_ne0 : x.biasedExp.val - 1 ≠ 0 := by omega
    suffices hsig : sigCeilOf q (x.biasedExp.val - 1) = 2^53 by
      rw [hsig]; unfold branchOfCeil; simp only [hbm1_ne0, ↓reduceIte]; norm_num
    have hbinexp : ((x.biasedExp.val - 1 : Nat) : Int) - 1075 = (x.biasedExp.val : Int) - 1076 := by omega
    simp only [show x.biasedExp.val > 1 from by omega, ↓reduceIte,
               show (4 * (2:Nat)^52 - 2) = (2^54 - 2 : Nat) from by norm_num] at hlo
    have hN : (2:Nat)^53 ≥ 1 := by norm_num
    exact sigCeilOf_eq_of_bounds q (x.biasedExp.val - 1) (2^53) hN
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact rtp_boundary_sigExact_lo_norm x.biasedExp.val q hbe_ge2 hlo)
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact rtp_boundary_sigExact_hi_norm x.biasedExp.val q hbe_ge2 hexp_lt hqlt)

theorem rtp_round_boundary (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_pos : 0 < q)
    (hs : x.sign = false)
    (hlo : scaleQ (4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4))
      (x.effectiveBinaryExp - 2) < q)
    (hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2))
    (hfbe_ne : F64.findBiasedExp q ≠ x.biasedExp.val) :
    F64.roundTowardPos q = x := by
  have hbexp := rtp_boundary_bexp_ge_one x hfin hne q hq_pos hhi hfbe_ne
  have hmant := rtp_boundary_mant_zero x hfin hne q hq_pos hlo hhi hfbe_ne
  have hfbe := rtp_boundary_fbe_eq x hfin hne q hq_pos hlo hhi hfbe_ne
  have hrs := rtp_boundary_roundSig x hfin hne q hq_pos hlo hhi hfbe_ne
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have habs_eq : |q| = q := abs_of_pos hq_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hpos : ¬(q < 0) := not_lt.mpr (le_of_lt hq_pos)
  unfold F64.roundTowardPos
  rw [if_neg hq_ne]
  simp only [if_neg hpos]
  rw [habs_eq, hfbe, hrs]
  simp only [ite_true]
  have hfinalExp : x.biasedExp.val - 1 + 1 = x.biasedExp.val := by omega
  rw [hfinalExp]
  have hlt_max : ¬(x.biasedExp.val ≥ F64.maxBiasedExp) := by unfold F64.maxBiasedExp; omega
  rw [if_neg hlt_max]
  unfold F64.mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt, show (0:Nat) < 2^52 from by norm_num, dite_true]
  have hdec : decide (q < 0) = false := decide_eq_false hpos
  rw [hdec]
  rcases x with ⟨s, ⟨be, hbe_bound⟩, ⟨m, hm_bound⟩⟩
  rw [F64.mk.injEq]
  refine ⟨by simp at hs; exact hs.symm, Fin.ext rfl, Fin.ext ?_⟩
  simp at hmant; exact hmant.symm

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
    have hmf_pos := rtp_effSig_pos x hfin hne
    have hd_le : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) ≤ 4 * x.effectiveSignificand := by
      split <;> omega
    unfold AcceptanceInterval.contains at hq
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    obtain ⟨hlo_raw, hhi_raw⟩ := hq
    -- Convert from inline if-then-else to scaleQ
    set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 2 else 4 : Nat) with hdelta_def
    have hlo : scaleQ (4 * x.effectiveSignificand - delta) (x.effectiveBinaryExp - 2) < q := hlo_raw
    have hhi : q ≤ scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2) := hhi_raw
    have hq_pos : 0 < q := by
      by_cases h0 : 4 * x.effectiveSignificand - delta = 0
      · rw [h0] at hlo; unfold scaleQ at hlo; simp at hlo; linarith
      · have := scaleQ_pos (4 * x.effectiveSignificand - delta) (by omega) (x.effectiveBinaryExp - 2)
        linarith
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    by_cases hfbe : F64.findBiasedExp q = x.biasedExp.val
    · exact rtp_round_same_exp x hfin hne q hq_ne hq_pos hs hlo hhi hfbe
    · exact rtp_round_boundary x hfin hne q hq_pos hs hlo hhi hfbe
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
