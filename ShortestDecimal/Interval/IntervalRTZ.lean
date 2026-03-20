/-
  Interval/IntervalRTZ.lean

  The acceptance interval for round-toward-zero (RTZ).
  Simpler than RNE: no tie-breaking, no boundary case.
-/
import ShortestDecimal.IEEE754.RoundProofRTZ
import ShortestDecimal.Interval.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace ShortestDecimal

-- Abbreviation to reduce casting pain
private def scaleQ (n : Nat) (e2 : Int) : ℚ :=
  if e2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ e2.toNat
  else (n : ℚ) / (2 : ℚ) ^ (-e2).toNat

/-- The RTZ acceptance interval. -/
def rtzInterval (x : F64) (_hfin : x.isFinite) : AcceptanceInterval :=
  let mf := x.effectiveSignificand
  let e2 := x.effectiveBinaryExp - 2
  if x.sign then
    { low := -(scaleQ (4 * mf + 4) e2), high := -(scaleQ (4 * mf) e2),
      lowInclusive := false, highInclusive := true }
  else
    { low := scaleQ (4 * mf) e2, high := scaleQ (4 * mf + 4) e2,
      lowInclusive := true, highInclusive := false }

private theorem rtz_effSig_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    x.effectiveSignificand ≥ 1 := by
  by_contra h; push_neg at h
  have : x.effectiveSignificand = 0 := by omega
  exact hne (by unfold F64.toRat; rw [if_neg (not_not.mpr hfin)]; simp [this])

private theorem scaleQ_pos (n : Nat) (hn : 0 < n) (e2 : Int) : 0 < scaleQ n e2 := by
  unfold scaleQ; split
  · exact mul_pos (by exact_mod_cast hn) (by positivity)
  · exact div_pos (by exact_mod_cast hn) (by positivity)

private theorem scaleQ_lt (a b : Nat) (h : a < b) (e2 : Int) : scaleQ a e2 < scaleQ b e2 := by
  unfold scaleQ; split
  · exact mul_lt_mul_of_pos_right (by exact_mod_cast h) (by positivity)
  · exact div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)

theorem rtz_abs_interval_pos (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    let iv := rtzInterval x hfin
    let absIv := if x.sign then
      { low := -iv.high, high := -iv.low,
        lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive : AcceptanceInterval }
    else iv
    0 < absIv.low ∧ absIv.low < absIv.high := by
  simp only []
  have hmf := rtz_effSig_pos x hfin hne
  cases hs : x.sign
  · unfold rtzInterval; simp only [hs, ite_false]
    exact ⟨scaleQ_pos _ (by omega) _, scaleQ_lt _ _ (by omega) _⟩
  · unfold rtzInterval; simp only [hs, ite_true, neg_neg]
    exact ⟨scaleQ_pos _ (by omega) _, scaleQ_lt _ _ (by omega) _⟩

/-! ## Pow helpers -/

private theorem pow_ef_cancel' (ef : Int) (hef2 : ¬(ef - 2 ≥ 0)) (hef : ef ≥ 0) :
    (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = 4 := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem pow_ef_cancel_neg' (ef : Int) (hef : ef < 0) :
    (2:ℚ) ^ (-ef).toNat * 4 = 2 ^ (-(ef - 2)).toNat := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

/-! ## Scaling: scaleQ(n, ef-2) ↔ n/4 in sigExact -/

private theorem rtz_sigExact_lower (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : scaleQ n (ef - 2) ≤ qAbs) :
    (n : ℚ) / 4 ≤
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  unfold scaleQ at hscale
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add]; congr 2; omega]
  · push_neg at hef2
    by_cases hef : ef ≥ 0
    · simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, if_pos hef] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right hle (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel' ef (by omega) hef]]
    · push_neg at hef
      simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, show ¬(ef ≥ 0) from by omega] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_iff₀ (by norm_num : (0:ℚ) < 4)]
      linarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg' ef (by omega)]]

private theorem rtz_sigExact_upper_strict (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs < scaleQ n (ef - 2)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) < (n : ℚ) / 4 := by
  unfold scaleQ at hscale
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add]; congr 2; omega]
  · push_neg at hef2
    by_cases hef : ef ≥ 0
    · simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, if_pos hef] at hscale ⊢
      have hlt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_lt_mul_of_pos_right hlt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel' ef (by omega) hef]]
    · push_neg at hef
      simp only [show ¬(ef - 2 ≥ 0) from by omega, ↓reduceIte, show ¬(ef ≥ 0) from by omega] at hscale ⊢
      have hlt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [lt_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg' ef (by omega)]]

/-! ## Floor lemma -/

private theorem floor_in_interval_rtz (n : ℕ) (hn : n ≥ 1) (sigExact : ℚ)
    (hlo : (n : ℚ) ≤ sigExact) (hhi : sigExact < (n : ℚ) + 1) :
    sigExact.floor.toNat = n := by
  have hfloor : ⌊sigExact⌋ = (n : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hlo, by push_cast; linarith⟩
  show sigExact.floor.toNat = n
  change ⌊sigExact⌋.toNat = n
  omega

/-! ## Decomposition -/

private def sigFloorOf (qAbs : ℚ) (bexp : Nat) : Nat :=
  let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
  let sigExact : ℚ := if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
                       else qAbs * (2 ^ (-binExp).toNat : ℚ)
  sigExact.floor.toNat

private def branchOfRTZ (sigFloor : Nat) (bexp : Nat) : Nat × Bool :=
  if bexp = 0 then
    if sigFloor ≥ 2^52 then (sigFloor - 2^52, true) else (sigFloor, false)
  else
    if sigFloor ≥ 2 * 2^52 then (sigFloor / 2 - 2^52, true)
    else if sigFloor < 2^52 then (sigFloor, false)
    else (sigFloor - 2^52, false)

private theorem roundSignificand_rtz_split (qAbs : ℚ) (bexp : Nat) :
    F64.roundSignificand_rtz qAbs bexp = branchOfRTZ (sigFloorOf qAbs bexp) bexp := rfl

private theorem branchOfRTZ_mf (x : F64) :
    branchOfRTZ x.effectiveSignificand x.biasedExp.val = (x.mantissa.val, false) := by
  unfold branchOfRTZ
  have hm := x.mantissa.isLt
  by_cases hbv : x.biasedExp.val = 0
  · simp only [hbv, ↓reduceIte]
    rw [F64.esig_subnormal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · simp only [hbv, ↓reduceIte]
    rw [F64.esig_normal x hbv]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]; exact ⟨by omega, trivial⟩

private theorem sigFloorOf_from_bounds (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (qAbs : ℚ)
    (hsig_lo : (x.effectiveSignificand : ℚ) ≤
      (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat))
    (hsig_hi : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) <
      (x.effectiveSignificand : ℚ) + 1) :
    sigFloorOf qAbs x.biasedExp.val = x.effectiveSignificand := by
  unfold sigFloorOf; simp only []; rw [F64.binExp_eq]
  exact floor_in_interval_rtz x.effectiveSignificand (rtz_effSig_pos x hfin hne) _ hsig_lo hsig_hi

/-! ## Extract |q| bounds -/

private theorem rtz_abs_bounds (x : F64) (hfin : x.isFinite)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (rtzInterval x hfin).contains q) :
    scaleQ (4 * x.effectiveSignificand) (x.effectiveBinaryExp - 2) ≤ |q| ∧
    |q| < scaleQ (4 * x.effectiveSignificand + 4) (x.effectiveBinaryExp - 2) := by
  unfold AcceptanceInterval.contains rtzInterval at hq; simp only [] at hq
  cases hs : x.sign
  · have hq_pos : 0 < q := by
      have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
    rw [abs_of_pos hq_pos]
    simp only [hs, ite_false, ite_true] at hq
    exact hq
  · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
    rw [abs_of_neg hq_neg]
    simp only [hs, Bool.false_eq_true, Bool.true_eq_false,
               ite_true, ite_false, neg_neg] at hq
    obtain ⟨hlo, hhi⟩ := hq
    constructor
    · linarith
    · linarith

/-! ## Threshold bounds -/

private theorem scaleQ_ge_threshQ (mf : Nat) (be : Nat) (hmf : mf ≥ 2^52)
    (hbe_ge : be ≥ 1) (hbe_lt : be < 2047) :
    F64.threshQ be ≤ scaleQ (4 * mf) ((be : Int) - 1077) := by
  unfold scaleQ
  have h4mf : (4 * mf : ℕ) ≥ 2^54 := by omega
  by_cases hge1077 : (be : Int) - 1077 ≥ 0
  · simp only [if_pos hge1077]
    have htonat : ((be : Int) - 1077).toNat = be - 1077 := by omega
    rw [htonat]
    unfold F64.threshQ; simp only [show be ≥ 1023 from by omega, ↓reduceIte]
    calc (2:ℚ) ^ (be - 1023) = 2^54 * 2^(be - 1077) := by
            rw [← pow_add]; congr 1; omega
      _ ≤ ↑(4 * mf) * 2^(be - 1077) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast h4mf
  · push_neg at hge1077
    simp only [show ¬((be : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 1077)).toNat = 1077 - be := by omega
    rw [htonat]
    unfold F64.threshQ
    by_cases hge1023 : be ≥ 1023
    · simp only [show be ≥ 1023 from hge1023, ↓reduceIte]
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(1077 - be))]
      calc (2:ℚ) ^ (be - 1023) * 2^(1077 - be) = 2^54 := by rw [← pow_add]; congr 1; omega
        _ ≤ (↑(4 * mf) : ℚ) := by exact_mod_cast h4mf
    · push_neg at hge1023
      simp only [show ¬(be ≥ 1023) from by omega, ↓reduceIte]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (2:ℚ) ^ (1077 - be) = 2^54 * 2^(1023 - be) := by rw [← pow_add]; congr 1; omega
        _ ≤ (↑(4 * mf) : ℚ) * 2^(1023 - be) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast h4mf

private theorem scaleQ_le_threshQ_succ (mf : Nat) (be : Nat)
    (hmf : mf < 2^53) (hbe_ge : be ≥ 1) (hbe_lt : be < 2047) :
    scaleQ (4 * mf + 4) ((be : Int) - 1077) ≤ F64.threshQ (be + 1) := by
  unfold scaleQ
  have hw_le : ((4 * mf + 4 : Nat) : ℚ) ≤ 2^55 := by
    exact_mod_cast (show (4 * mf + 4 : ℕ) ≤ 2^55 from by omega)
  by_cases hge1077 : (be : Int) - 1077 ≥ 0
  · simp only [if_pos hge1077]
    have htonat : ((be : Int) - 1077).toNat = be - 1077 := by omega
    rw [htonat]
    unfold F64.threshQ; simp only [show be + 1 ≥ 1023 from by omega, ↓reduceIte]
    calc ↑(4 * mf + 4) * (2:ℚ)^(be - 1077)
        ≤ 2^55 * 2^(be - 1077) := mul_le_mul_of_nonneg_right hw_le (by positivity)
      _ = 2^(be + 1 - 1023) := by rw [← pow_add]; congr 1; omega
  · push_neg at hge1077
    simp only [show ¬((be : Int) - 1077 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 1077)).toNat = 1077 - be := by omega
    rw [htonat]
    unfold F64.threshQ
    by_cases hge1022 : be + 1 ≥ 1023
    · simp only [show be + 1 ≥ 1023 from hge1022, ↓reduceIte]
      rw [div_le_iff₀ (by positivity : (0:ℚ) < 2^(1077 - be))]
      calc (↑(4 * mf + 4) : ℚ) ≤ 2^55 := hw_le
        _ = 2^(be + 1 - 1023) * 2^(1077 - be) := by rw [← pow_add]; congr 1; omega
    · push_neg at hge1022
      simp only [show ¬(be + 1 ≥ 1023) from by omega, ↓reduceIte]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (↑(4 * mf + 4) : ℚ) * 2^(1023 - (be + 1))
          ≤ 2^55 * 2^(1023 - (be + 1)) := mul_le_mul_of_nonneg_right hw_le (by positivity)
        _ = 2^(1077 - be) := by rw [← pow_add]; congr 1; omega

private theorem subnormal_le_threshQ1 (mf : Nat) (hmf : mf < 2^52) :
    scaleQ (4 * mf + 4) (-1076) ≤ F64.threshQ 1 := by
  unfold scaleQ
  simp only [show ¬((-1076 : Int) ≥ 0) from by omega, ↓reduceIte,
             show ((-(-1076 : Int)).toNat) = 1076 from by omega]
  unfold F64.threshQ; simp only [show ¬(1 ≥ 1023) from by omega, ↓reduceIte,
                                 show 1023 - 1 = 1022 from by omega]
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have hle : ((4 * mf + 4 : Nat) : ℚ) ≤ 2^54 := by
    exact_mod_cast (show (4 * mf + 4 : ℕ) ≤ 2^54 from by omega)
  calc ((4 * mf + 4 : Nat) : ℚ) * 2^1022
      ≤ (2^54 : ℚ) * 2^1022 := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 2^1076 := by rw [← pow_add]

/-! ## findBiasedExp correct for RTZ -/

set_option maxHeartbeats 800000 in
private theorem rtz_findBiasedExp_correct (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (rtzInterval x hfin).contains q) :
    F64.findBiasedExp |q| = x.biasedExp.val := by
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  have ⟨habs_lo, habs_hi⟩ := rtz_abs_bounds x hfin q hq_ne hdec hq
  by_cases hbexp0 : x.biasedExp.val = 0
  · have hesig_lt : x.effectiveSignificand < 2^52 := by
      unfold F64.effectiveSignificand; simp [hbexp0]
    have he2 : x.effectiveBinaryExp - 2 = -1076 := by
      unfold F64.effectiveBinaryExp F64.expBias F64.mantBits; simp [hbexp0]
    rw [he2] at habs_hi
    have hq_lt : |q| < F64.threshQ 1 :=
      lt_of_lt_of_le habs_hi (subnormal_le_threshQ1 x.effectiveSignificand hesig_lt)
    unfold F64.findBiasedExp; apply F64.go_eq
    · omega
    · left; exact hbexp0
    · intro e he hle; push_neg
      calc |q| < F64.threshQ 1 := hq_lt
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)
  · have hbexp_ge : x.biasedExp.val ≥ 1 := by omega
    have hesig_ge : x.effectiveSignificand ≥ 2^52 := by
      unfold F64.effectiveSignificand; simp [hbexp0, F64.mantBits]
    have hesig_lt_nat : x.effectiveSignificand < 2^53 := by
      have h := F64.effectiveSignificand_lt x hfin; omega
    have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 1077 := by
      rw [F64.ebe_normal x hbexp0]; ring
    rw [he2] at habs_lo habs_hi
    have hge : F64.threshQ x.biasedExp.val ≤ |q| :=
      le_trans (scaleQ_ge_threshQ _ _ hesig_ge hbexp_ge hexp_lt) habs_lo
    have hlt : |q| < F64.threshQ (x.biasedExp.val + 1) :=
      lt_of_lt_of_le habs_hi (scaleQ_le_threshQ_succ _ _ hesig_lt_nat hbexp_ge hexp_lt)
    unfold F64.findBiasedExp; apply F64.go_eq
    · omega
    · right; exact hge
    · intro e hgt hle; push_neg
      calc |q| < F64.threshQ (x.biasedExp.val + 1) := hlt
        _ ≤ F64.threshQ e := F64.threshQ_le_of_le (by omega)

/-! ## Main soundness -/

private theorem rtz_round_core (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (rtzInterval x hfin).contains q)
    (hfbe : F64.findBiasedExp |q| = x.biasedExp.val) :
    F64.roundTowardZero q = x := by
  have hexp_lt := F64.finite_implies_exp_lt x hfin
  unfold F64.roundTowardZero; rw [if_neg hq_ne]; simp only []; rw [hfbe]
  have hrs : F64.roundSignificand_rtz |q| x.biasedExp.val = (x.mantissa.val, false) := by
    rw [roundSignificand_rtz_split]
    have hmf_pos := rtz_effSig_pos x hfin hne
    have ⟨habs_lo, habs_hi⟩ := rtz_abs_bounds x hfin q hq_ne hdec hq
    have hsig_lo := rtz_sigExact_lower (4 * x.effectiveSignificand) |q| x.effectiveBinaryExp habs_lo
    have hsig_hi := rtz_sigExact_upper_strict (4 * x.effectiveSignificand + 4) |q| x.effectiveBinaryExp habs_hi
    have hu_eq : ((4 * x.effectiveSignificand : ℕ) : ℚ) / 4 = (x.effectiveSignificand : ℚ) := by
      push_cast; ring
    have hw_eq : ((4 * x.effectiveSignificand + 4 : ℕ) : ℚ) / 4 = (x.effectiveSignificand : ℚ) + 1 := by
      push_cast; ring
    have hsig := sigFloorOf_from_bounds x hfin hne |q|
      (by rw [← hu_eq]; exact hsig_lo)
      (by rw [← hw_eq]; exact hsig_hi)
    rw [hsig]; exact branchOfRTZ_mf x
  rw [hrs]; simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold F64.maxBiasedExp; omega)]
  unfold F64.mkFinite
  simp only [show x.biasedExp.val < 2047 from hexp_lt,
             show x.mantissa.val < 2^52 from x.mantissa.isLt, dite_true]
  rw [hdec]

theorem rtz_interval_correct (x : F64) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0)
    (q : ℚ) (hq : (rtzInterval x hfin).contains q) :
    F64.roundTowardZero q = x := by
  have hq_ne : q ≠ 0 := by
    intro heq; subst heq
    have ⟨hlo_pos, _⟩ := rtz_abs_interval_pos x hfin hne
    unfold AcceptanceInterval.contains at hq
    cases hs : x.sign <;> simp [hs] at hlo_pos hq
    · obtain ⟨h, _⟩ := hq; split at h <;> linarith
    · obtain ⟨_, h⟩ := hq; split at h <;> linarith
  have hdec : decide (q < 0) = x.sign := by
    have ⟨hlo_pos, _⟩ := rtz_abs_interval_pos x hfin hne
    have hqc := hq
    unfold AcceptanceInterval.contains at hqc
    cases hs : x.sign <;> simp [hs] at hlo_pos hqc
    · obtain ⟨h, _⟩ := hqc
      have : 0 < q := by split at h <;> linarith
      exact decide_eq_false (by linarith)
    · obtain ⟨_, h⟩ := hqc
      have : q < 0 := by split at h <;> linarith
      exact decide_eq_true this
  have hfbe := rtz_findBiasedExp_correct x hfin hne q hq_ne hdec hq
  exact rtz_round_core x hfin hne q hq_ne hdec hq hfbe

end ShortestDecimal
