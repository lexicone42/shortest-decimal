/-
  Interval/Interval32.lean

  The acceptance interval: for a finite F32 x, the set of rationals
  that round to x under round-to-nearest-even.

  This mirrors Interval.lean (F64) with F32 constants.
-/
import ShortestDecimal.IEEE754.RoundProof32
import ShortestDecimal.Interval.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ShortestDecimal

-- Reuse AcceptanceInterval from Interval.lean (imported)

/-- Predecessor of an F32 value. -/
def f32Pred (x : F32) : F32 :=
  if x.mantissa.val > 0 then
    ⟨x.sign, x.biasedExp, ⟨x.mantissa.val - 1, by omega⟩⟩
  else if h : x.biasedExp.val > 0 then
    ⟨x.sign, ⟨x.biasedExp.val - 1, by omega⟩, ⟨2^23 - 1, by omega⟩⟩
  else
    ⟨!x.sign, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Successor of an F32 value. -/
def f32Succ (x : F32) : F32 :=
  if h : x.mantissa.val + 1 < 2^23 then
    ⟨x.sign, x.biasedExp, ⟨x.mantissa.val + 1, h⟩⟩
  else if h2 : x.biasedExp.val + 1 < 256 then
    ⟨x.sign, ⟨x.biasedExp.val + 1, h2⟩, ⟨0, by omega⟩⟩
  else
    ⟨x.sign, ⟨255, by omega⟩, ⟨0, by omega⟩⟩

/-- Compute the acceptance interval for a finite F32 value.
    Based on the algebraic (u, v, w) · 2^e₂ representation from the Ryu paper (Section 2.2).
    u = 4·mf - δ, w = 4·mf + 2, e₂ = ef - 2
    δ = 1 if mantissa=0 and biasedExp>1 (exponent boundary), else δ = 2. -/
def schubfachInterval32 (x : F32) (_hfin : x.isFinite) : AcceptanceInterval :=
  let mf := x.effectiveSignificand
  let e2 := x.effectiveBinaryExp - 2
  let delta : Nat := if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2
  let u : Nat := 4 * mf - delta
  let w : Nat := 4 * mf + 2
  let mantEven := x.mantissa.val % 2 = 0
  let scaleN (n : Nat) : ℚ :=
    if e2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ e2.toNat
    else (n : ℚ) / (2 : ℚ) ^ (-e2).toNat
  if x.sign then
    { low := -(scaleN w), high := -(scaleN u),
      lowInclusive := mantEven, highInclusive := mantEven }
  else
    { low := scaleN u, high := scaleN w,
      lowInclusive := mantEven, highInclusive := mantEven }

/-! ## Helper lemmas -/

private theorem effSig_pos_of_toRat_ne_zero32 (x : F32) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) : x.effectiveSignificand ≥ 1 := by
  by_contra h; push_neg at h
  have : x.effectiveSignificand = 0 := by omega
  exact hne (by unfold F32.toRat; rw [if_neg (not_not.mpr hfin)]; simp [this])

private theorem scaleN_pos_and_lt32 {u w : Nat} (hu : 0 < u) (hw : u < w) (e2 : Int) :
    0 < (if e2 ≥ 0 then (u : ℚ) * (2 : ℚ) ^ e2.toNat
         else (u : ℚ) / (2 : ℚ) ^ (-e2).toNat) ∧
    (if e2 ≥ 0 then (u : ℚ) * (2 : ℚ) ^ e2.toNat
     else (u : ℚ) / (2 : ℚ) ^ (-e2).toNat) <
    (if e2 ≥ 0 then (w : ℚ) * (2 : ℚ) ^ e2.toNat
     else (w : ℚ) / (2 : ℚ) ^ (-e2).toNat) := by
  by_cases he : e2 ≥ 0
  · simp only [if_pos he]
    exact ⟨mul_pos (by exact_mod_cast hu) (by positivity),
           mul_lt_mul_of_pos_right (by exact_mod_cast hw) (by positivity)⟩
  · simp only [if_neg he]
    exact ⟨div_pos (by exact_mod_cast hu) (by positivity),
           div_lt_div_of_pos_right (by exact_mod_cast hw) (by positivity)⟩

/-- The absolute interval has strictly positive bounds with low < high. -/
theorem schubfach_abs_interval_pos32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0) :
    let iv := schubfachInterval32 x hfin
    let absIv := if x.sign then
      { low := -iv.high, high := -iv.low,
        lowInclusive := iv.highInclusive, highInclusive := iv.lowInclusive : AcceptanceInterval }
    else iv
    0 < absIv.low ∧ absIv.low < absIv.high := by
  simp only []
  have hmf := effSig_pos_of_toRat_ne_zero32 x hfin hne
  have hu_pos : 0 < 4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) := by
    split <;> omega
  have hw_gt : 4 * x.effectiveSignificand -
      (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) <
      4 * x.effectiveSignificand + 2 := by
    split <;> omega
  have key := scaleN_pos_and_lt32 hu_pos hw_gt (x.effectiveBinaryExp - 2)
  cases hs : x.sign
  · unfold schubfachInterval32; simp only [hs, Bool.false_eq_true, ite_false]; exact key
  · unfold schubfachInterval32; simp only [hs, Bool.true_eq_false, ite_false, ite_true, neg_neg]; exact key

/-! ## Core rounding lemma -/

/-- Rounding in [n - 1/2, n + 1/2] with tie-break to even gives n. -/
private theorem round_in_half_interval32 (n : ℕ) (hn : n ≥ 1) (sigExact : ℚ)
    (hlo : (n : ℚ) - 1/2 ≤ sigExact)
    (hhi : sigExact ≤ (n : ℚ) + 1/2)
    (hlo_strict : sigExact = (n : ℚ) - 1/2 → n % 2 = 0)
    (hhi_strict : sigExact = (n : ℚ) + 1/2 → n % 2 = 0) :
    let sigFloor := sigExact.floor.toNat
    let remainder := sigExact - sigFloor
    (if remainder < 1/2 then sigFloor
     else if remainder > 1/2 then sigFloor + 1
     else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1) = n := by
  simp only []
  have hn_cast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    exact_mod_cast this
  by_cases hge : sigExact ≥ (n : ℚ)
  · have hfloor : sigExact.floor = (n : ℤ) := by
      show ⌊sigExact⌋ = ↑n
      rw [Int.floor_eq_iff]; exact ⟨by exact_mod_cast hge, by push_cast; linarith⟩
    have htonat : sigExact.floor.toNat = n := by omega
    rw [htonat]
    by_cases hrem_lt : sigExact - (n : ℚ) < 1/2
    · rw [if_pos hrem_lt]
    · push_neg at hrem_lt
      rw [if_neg (by linarith), if_neg (by linarith)]
      rw [if_pos (hhi_strict (by linarith))]
  · push_neg at hge
    have hfloor : sigExact.floor = (n : ℤ) - 1 := by
      show ⌊sigExact⌋ = ↑n - 1
      rw [Int.floor_eq_iff]; exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    have htonat : sigExact.floor.toNat = n - 1 := by omega
    rw [htonat]
    by_cases hrem_eq : sigExact = (n : ℚ) - 1/2
    · have hmod := hlo_strict hrem_eq
      have hmod1 : (n - 1) % 2 = 1 := by omega
      rw [if_neg (by rw [hrem_eq, hn_cast]; linarith)]
      rw [if_neg (by rw [hrem_eq, hn_cast]; linarith)]
      rw [if_neg (by rw [hmod1]; omega)]
      omega
    · have hlt : sigExact > (n : ℚ) - 1/2 := lt_of_le_of_ne hlo (Ne.symm hrem_eq)
      have hrem_gt : sigExact - ((n - 1 : ℕ) : ℚ) > 1/2 := by rw [hn_cast]; linarith
      rw [if_neg (by linarith), if_pos hrem_gt]
      omega

/-- Helper: if sigExact ∈ [N - 1/2, N) with N-1 odd, then the rounding gives N. -/
private theorem round_to_N32 (N : Nat) (sigExact : ℚ)
    (hlo : (N : ℚ) - 1/2 ≤ sigExact) (hhi : sigExact < N)
    (hN_ge : N ≥ 2) (hN_odd_pred : (N - 1) % 2 = 1) :
    let sigFloor := sigExact.floor.toNat
    let remainder := sigExact - sigFloor
    (if remainder < 1/2 then sigFloor
     else if remainder > 1/2 then sigFloor + 1
     else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1) = N := by
  simp only []
  -- floor = N - 1
  have hfloor : sigExact.floor = ((N : Int) - 1) := by
    rw [show sigExact.floor = ⌊sigExact⌋ from rfl, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have htonat : sigExact.floor.toNat = N - 1 := by rw [hfloor]; omega
  rw [htonat]
  -- remainder ≥ 1/2
  have hrem_ge : sigExact - ((N - 1 : Nat) : ℚ) ≥ 1/2 := by
    have : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
      have : ((N - 1 : Nat) : ℤ) = (N : ℤ) - 1 := by omega
      exact_mod_cast this
    rw [this]; linarith
  rw [if_neg (by linarith)]
  by_cases hrem_gt : sigExact - ((N - 1 : Nat) : ℚ) > 1/2
  · rw [if_pos hrem_gt]; omega
  · push_neg at hrem_gt
    rw [if_neg (by linarith)]
    -- floor = N-1, which is odd
    rw [if_neg (by omega)]
    omega

/-! ## Decomposing roundSignificand -/

/-- The rounding step of roundSignificand: compute sigExact, round to nearest even. -/
private def sigRoundedOf32 (qAbs : ℚ) (bexp : Nat) : Nat :=
  let binExp : Int := if bexp = 0 then -149 else (bexp : Int) - 150
  let sigExact : ℚ := if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
                       else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  if remainder < 1/2 then sigFloor
  else if remainder > 1/2 then sigFloor + 1
  else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1

/-- The branch analysis: convert sigRounded to (mantissa, bumpExp). -/
private def branchOf32 (sigRounded : Nat) (bexp : Nat) : Nat × Bool :=
  if bexp = 0 then
    if sigRounded ≥ 2^23 then (sigRounded - 2^23, true) else (sigRounded, false)
  else
    if sigRounded ≥ 2 * 2^23 then (sigRounded / 2 - 2^23, true)
    else if sigRounded < 2^23 then (sigRounded, false)
    else (sigRounded - 2^23, false)

private theorem roundSignificand_split32 (qAbs : ℚ) (bexp : Nat) :
    F32.roundSignificand qAbs bexp = branchOf32 (sigRoundedOf32 qAbs bexp) bexp := rfl

private theorem branchOf_mf32 (x : F32) :
    branchOf32 x.effectiveSignificand x.biasedExp.val = (x.mantissa.val, false) := by
  unfold branchOf32
  have hm := x.mantissa.isLt
  split
  · next hbe =>
    rw [F32.esig_subnormal x (by omega)]
    split
    · next hge => exact absurd hm (by omega)
    · rfl
  · next hbe =>
    rw [F32.esig_normal x (by omega)]
    split
    · next hge => exact absurd hm (by omega)
    · split
      · next hlt => exact absurd hlt (by omega)
      · simp only [Prod.mk.injEq]; exact ⟨by omega, trivial⟩

/-! ## Scaling lemmas -/

private theorem pow_ef_cancel32 (ef : Int) (hef2 : ¬(ef - 2 ≥ 0)) (hef : ef ≥ 0) :
    (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = 4 := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem pow_ef_cancel_neg32 (ef : Int) (hef : ef < 0) :
    (2:ℚ) ^ (-ef).toNat * 4 = 2 ^ (-(ef - 2)).toNat := by
  rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_add]; congr 1; omega

private theorem sigExact_lower_bound32 (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat) ≤ qAbs) :
    (n : ℚ) / 4 ≤
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    linarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right hle (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel32 ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hle := (div_le_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_iff₀ (by norm_num : (0:ℚ) < 4)]
      linarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg32 ef (by omega)]]

private theorem sigExact_upper_bound32 (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs ≤ (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) ≤ (n : ℚ) / 4 := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    linarith [mul_le_mul_of_nonneg_right hscale (show (0:ℚ) ≤ 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hge := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [mul_le_mul_of_nonneg_right hge (show (0:ℚ) ≤ 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel32 ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hge := (le_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [le_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      linarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg32 ef (by omega)]]

private theorem sigExact_lower_bound_strict32 (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat) < qAbs) :
    (n : ℚ) / 4 <
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_right hlt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel32 ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hlt := (div_lt_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg32 ef (by omega)]]

private theorem sigExact_upper_bound_strict32 (n : ℕ) (qAbs : ℚ) (ef : Int)
    (hscale : qAbs < (if ef - 2 ≥ 0 then (n : ℚ) * (2 : ℚ) ^ (ef - 2).toNat
               else (n : ℚ) / (2 : ℚ) ^ (-(ef - 2)).toNat)) :
    (if ef ≥ 0 then qAbs / (2 : ℚ) ^ ef.toNat
     else qAbs * (2 : ℚ) ^ (-ef).toNat) < (n : ℚ) / 4 := by
  by_cases hef2 : ef - 2 ≥ 0
  · have hef : ef ≥ 0 := by omega
    simp only [if_pos hef2, if_pos hef] at hscale ⊢
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hexp : (ef - 2).toNat + 2 = ef.toNat := by omega
    nlinarith [mul_lt_mul_of_pos_right hscale (show (0:ℚ) < 2^2 from by positivity),
              show (n : ℚ) * 2 ^ (ef - 2).toNat * 2 ^ 2 = n * 2 ^ ef.toNat from by
                rw [mul_assoc, ← pow_add, hexp]]
  · push_neg at hef2
    have hef2' : ¬(ef - 2 ≥ 0) := by omega
    by_cases hef : ef ≥ 0
    · simp only [if_neg hef2', if_pos hef] at hscale ⊢
      have hgt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_lt_mul_of_pos_right hgt (show (0:ℚ) < 2 ^ ef.toNat from by positivity),
                show qAbs * (2:ℚ) ^ (-(ef - 2)).toNat * 2 ^ ef.toNat = qAbs * 4 from by
                  rw [mul_assoc, pow_ef_cancel32 ef hef2' hef]]
    · push_neg at hef
      simp only [if_neg hef2', if_neg (show ¬(ef ≥ 0) from by omega)] at hscale ⊢
      have hgt := (lt_div_iff₀ (show (0:ℚ) < 2 ^ (-(ef - 2)).toNat from by positivity)).mp hscale
      rw [lt_div_iff₀ (by norm_num : (0:ℚ) < 4)]
      nlinarith [show qAbs * (2:ℚ) ^ (-ef).toNat * 4 = qAbs * 2 ^ (-(ef - 2)).toNat from by
                  rw [mul_assoc, pow_ef_cancel_neg32 ef (by omega)]]

/-- sigRoundedOf32 = effectiveSignificand when sigExact ∈ [mf - 1/2, mf + 1/2]. -/
private theorem sigRoundedOf_from_bounds32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (qAbs : ℚ)
    (hsig_lo : (x.effectiveSignificand : ℚ) - 1/2 ≤
      (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat))
    (hsig_hi : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) ≤
      (x.effectiveSignificand : ℚ) + 1/2)
    (hlo_even : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) =
      (x.effectiveSignificand : ℚ) - 1/2 → x.effectiveSignificand % 2 = 0)
    (hhi_even : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) =
      (x.effectiveSignificand : ℚ) + 1/2 → x.effectiveSignificand % 2 = 0) :
    sigRoundedOf32 qAbs x.biasedExp.val = x.effectiveSignificand := by
  unfold sigRoundedOf32; simp only []; rw [F32.binExp_eq]
  exact round_in_half_interval32 x.effectiveSignificand
    (effSig_pos_of_toRat_ne_zero32 x hfin hne) _ hsig_lo hsig_hi hlo_even hhi_even

/-! ## Interval soundness -/

/-! ### Case A: same biased exponent -/

/-- Case A: when findBiasedExp returns the same exponent as x,
    roundSignificand recovers x's mantissa. -/
private theorem interval_round_same_exp32 (x : F32) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe : F32.findBiasedExp |q| = x.biasedExp.val) :
    F32.roundToNearestEven q = x := by
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  unfold F32.roundToNearestEven
  rw [if_neg hq_ne]
  simp only []
  rw [hfbe]
  have hrs : F32.roundSignificand |q| x.biasedExp.val = (x.mantissa.val, false) := by
    rw [roundSignificand_split32]
    set mf := x.effectiveSignificand
    set ef := x.effectiveBinaryExp
    set e2 := ef - 2
    set delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat)
    set u := 4 * mf - delta
    set w := 4 * mf + 2
    have hmf_pos := effSig_pos_of_toRat_ne_zero32 x hfin hne
    have hdelta_le : delta ≤ 2 := by
      show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 2; split <;> omega
    -- Extract |q| bounds from interval membership
    have habs_lo : (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat
                    else (u : ℚ) / 2 ^ (-e2).toNat) ≤ |q| := by
      unfold AcceptanceInterval.contains schubfachInterval32 at hq
      simp only [] at hq
      cases hs : x.sign
      · have hq_pos : 0 < q := by
          have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
          exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
        rw [abs_of_pos hq_pos]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨hlo, _⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
        · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
      · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
        rw [abs_of_neg hq_neg]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨_, hhi⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
        · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
    have habs_hi : |q| ≤ (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat
                           else (w : ℚ) / 2 ^ (-e2).toNat) := by
      unfold AcceptanceInterval.contains schubfachInterval32 at hq
      simp only [] at hq
      cases hs : x.sign
      · have hq_pos : 0 < q := by
          have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
          exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
        rw [abs_of_pos hq_pos]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨_, hhi⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
        · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
      · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
        rw [abs_of_neg hq_neg]
        simp only [hs, Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true] at hq; obtain ⟨hlo, _⟩ := hq
        by_cases he2 : e2 ≥ 0
        · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
        · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
    -- Apply scaling lemmas
    have hsig_lo := sigExact_lower_bound32 u |q| ef habs_lo
    have hsig_hi := sigExact_upper_bound32 w |q| ef habs_hi
    -- u/4 ≥ mf - 1/2
    have hu_lower : (mf : ℚ) - 1/2 ≤ (u : ℚ) / 4 := by
      have hsub : delta ≤ 4 * mf := by
        show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 4 * mf
        split <;> omega
      show (mf : ℚ) - 1/2 ≤ ((4 * mf - delta : ℕ) : ℚ) / 4
      push_cast [Nat.cast_sub hsub]
      linarith [show (delta : ℚ) ≤ 2 from by exact_mod_cast hdelta_le]
    -- w/4 = mf + 1/2
    have hw_eq : (w : ℚ) / 4 = (mf : ℚ) + 1/2 := by
      show ((4 * mf + 2 : ℕ) : ℚ) / 4 = (mf : ℚ) + 1/2; push_cast; ring
    -- Tie-breaking: lower boundary
    have hlo_even : (if ef ≥ 0 then |q| / (2:ℚ) ^ ef.toNat
                     else |q| * (2:ℚ) ^ (-ef).toNat) =
                    (mf : ℚ) - 1/2 → mf % 2 = 0 := by
      intro heq
      have hu_eq : (u : ℚ) / 4 = (mf : ℚ) - 1/2 :=
        le_antisymm (by linarith [heq, hsig_lo]) hu_lower
      have hdelta2 : delta = 2 := by
        have hsub : delta ≤ 4 * mf := by
          show (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) ≤ 4 * mf
          split <;> omega
        have h_eq : (u : ℚ) = ((4 * mf - delta : ℕ) : ℚ) := by rfl
        rw [h_eq] at hu_eq
        push_cast [Nat.cast_sub hsub] at hu_eq
        have : (delta : ℚ) = 2 := by linarith
        exact_mod_cast this
      by_contra h_not_even
      have h_odd : x.mantissa.val % 2 ≠ 0 := by
        by_cases hbexp : x.biasedExp.val = 0
        · rwa [show mf = x.mantissa.val from F32.esig_subnormal x hbexp] at h_not_even
        · rw [show mf = 2^23 + x.mantissa.val from F32.esig_normal x hbexp] at h_not_even
          intro h; exact h_not_even (by omega)
      -- Extract strict lower bound from interval with odd mantissa
      have habs_strict : (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat
                          else (u : ℚ) / 2 ^ (-e2).toNat) < |q| := by
        unfold AcceptanceInterval.contains schubfachInterval32 at hq
        simp only [] at hq
        cases hs : x.sign
        · have hq_pos : 0 < q := by
            have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
            exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
          rw [abs_of_pos hq_pos]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨hlo, _⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
          · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
        · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
          rw [abs_of_neg hq_neg]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨_, hhi⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
          · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
      linarith [sigExact_lower_bound_strict32 u |q| ef habs_strict]
    -- Tie-breaking: upper boundary
    have hhi_even : (if ef ≥ 0 then |q| / (2:ℚ) ^ ef.toNat
                     else |q| * (2:ℚ) ^ (-ef).toNat) =
                    (mf : ℚ) + 1/2 → mf % 2 = 0 := by
      intro heq
      by_contra h_not_even
      have h_odd : x.mantissa.val % 2 ≠ 0 := by
        by_cases hbexp : x.biasedExp.val = 0
        · rwa [show mf = x.mantissa.val from F32.esig_subnormal x hbexp] at h_not_even
        · rw [show mf = 2^23 + x.mantissa.val from F32.esig_normal x hbexp] at h_not_even
          intro h; exact h_not_even (by omega)
      -- Extract strict upper bound
      have habs_strict : |q| < (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat
                                else (w : ℚ) / 2 ^ (-e2).toNat) := by
        unfold AcceptanceInterval.contains schubfachInterval32 at hq
        simp only [] at hq
        cases hs : x.sign
        · have hq_pos : 0 < q := by
            have : ¬(q < 0) := of_decide_eq_false (by rw [hdec, hs])
            exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hq_ne)
          rw [abs_of_pos hq_pos]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨_, hhi⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
          · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
        · have hq_neg : q < 0 := of_decide_eq_true (by rw [hdec, hs])
          rw [abs_of_neg hq_neg]
          simp only [hs, show ¬(x.mantissa.val % 2 = 0) from h_odd,
            Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true,
            decide_eq_false_iff_not, decide_eq_true_eq] at hq
          obtain ⟨hlo, _⟩ := hq
          by_cases he2 : e2 ≥ 0
          · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
          · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
      linarith [sigExact_upper_bound_strict32 w |q| ef habs_strict]
    -- Apply sigRoundedOf_from_bounds32
    have hsig := sigRoundedOf_from_bounds32 x hfin hne |q|
      (le_trans hu_lower hsig_lo) (by rw [← hw_eq]; exact hsig_hi)
      hlo_even hhi_even
    rw [hsig]
    exact branchOf_mf32 x
  -- Step 2: Use hrs to finish
  rw [hrs]
  simp only [show (false = true) = False from by decide, ite_false]
  rw [if_neg (by unfold F32.maxBiasedExp; omega)]
  unfold F32.mkFinite
  simp only [show x.biasedExp.val < 255 from hexp_lt,
             show x.mantissa.val < 2^23 from x.mantissa.isLt, dite_true]
  rw [hdec]

/-! ### Case B: boundary case -/

private theorem pos_of_sign_false32 {x : F32} (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign) (hs : x.sign = false) : 0 < q := by
  have h1 : decide (q < 0) = false := hdec.trans hs
  have hnneg : ¬(q < 0) := decide_eq_false_iff_not.mp h1
  exact lt_of_le_of_ne (not_lt.mp hnneg) (Ne.symm hq_ne)

private theorem neg_of_sign_true32 {x : F32} (q : ℚ)
    (hdec : decide (q < 0) = x.sign) (hs : x.sign = true) : q < 0 := by
  have h1 : decide (q < 0) = true := hdec.trans hs
  exact decide_eq_true_iff.mp h1

/-- Extract |q| bounds from schubfachInterval32. -/
private theorem interval_abs_bounds32 (x : F32) (hfin : x.isFinite)
    (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q) :
    let mf := x.effectiveSignificand
    let e2 := x.effectiveBinaryExp - 2
    let delta := (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat)
    let u := 4 * mf - delta
    let w := 4 * mf + 2
    (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat else (u : ℚ) / 2 ^ (-e2).toNat) ≤ |q| ∧
    |q| ≤ (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat else (w : ℚ) / 2 ^ (-e2).toNat) := by
  simp only []
  unfold AcceptanceInterval.contains schubfachInterval32 at hq; simp only [] at hq
  cases hs : x.sign
  · have hq_pos := pos_of_sign_false32 q hq_ne hdec hs
    rw [abs_of_pos hq_pos]
    simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hq
    obtain ⟨hlo, hhi⟩ := hq
    constructor
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
      · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
      · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
  · have hq_neg := neg_of_sign_true32 q hdec hs
    rw [abs_of_neg hq_neg]
    simp only [hs, Bool.true_eq_false, ite_true] at hq
    obtain ⟨hlo, hhi⟩ := hq
    constructor
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hhi ⊢; split at hhi <;> linarith
      · simp only [if_neg he2] at hhi ⊢; split at hhi <;> linarith
    · by_cases he2 : x.effectiveBinaryExp - 2 ≥ 0
      · simp only [if_pos he2] at hlo ⊢; split at hlo <;> linarith
      · simp only [if_neg he2] at hlo ⊢; split at hlo <;> linarith

/-- If u ≥ 2^25 and e2 = be - 152, then scaleN(u, e2) ≥ threshQ(be). -/
private theorem scaleN_ge_threshQ32 (u : Nat) (be : Nat) (hu : u ≥ 2^25)
    (hbe_ge : be ≥ 1) (hbe_lt : be < 255) :
    let e2 : Int := (be : Int) - 152
    F32.threshQ be ≤ (if e2 ≥ 0 then (u : ℚ) * 2 ^ e2.toNat else (u : ℚ) / 2 ^ (-e2).toNat) := by
  simp only []
  by_cases hge152 : (be : Int) - 152 ≥ 0
  · simp only [if_pos hge152]
    have htonat : ((be : Int) - 152).toNat = be - 152 := by omega
    rw [htonat]
    unfold F32.threshQ; simp only [show be ≥ 127 from by omega, ↓reduceIte]
    calc (2:ℚ) ^ (be - 127)
        = 2^25 * 2^(be - 152) := by rw [← pow_add]; congr 1; omega
      _ ≤ (u : ℚ) * 2^(be - 152) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hu
  · push_neg at hge152
    simp only [show ¬((be : Int) - 152 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 152)).toNat = 152 - be := by omega
    rw [htonat]
    unfold F32.threshQ
    by_cases hge127 : be ≥ 127
    · simp only [show be ≥ 127 from hge127, ↓reduceIte]
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(152 - be))]
      calc (2:ℚ) ^ (be - 127) * 2^(152 - be) = 2^25 := by rw [← pow_add]; congr 1; omega
        _ ≤ (u : ℚ) := by exact_mod_cast hu
    · push_neg at hge127
      simp only [show ¬(be ≥ 127) from by omega, ↓reduceIte]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (2:ℚ) ^ (152 - be)
          = 2^25 * 2^(127 - be) := by rw [← pow_add]; congr 1; omega
        _ ≤ (u : ℚ) * 2^(127 - be) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hu

/-- If w < 2^26 and e2 = be - 152, then scaleN(w, e2) < threshQ(be+1). -/
private theorem scaleN_lt_threshQ_succ32 (w : Nat) (be : Nat) (hw : (w : ℚ) < 2^26)
    (hbe_ge : be ≥ 1) (hbe_lt : be < 255) :
    let e2 : Int := (be : Int) - 152
    (if e2 ≥ 0 then (w : ℚ) * 2 ^ e2.toNat else (w : ℚ) / 2 ^ (-e2).toNat) < F32.threshQ (be + 1) := by
  simp only []
  by_cases hge152 : (be : Int) - 152 ≥ 0
  · simp only [if_pos hge152]
    have htonat : ((be : Int) - 152).toNat = be - 152 := by omega
    rw [htonat]
    unfold F32.threshQ; simp only [show be + 1 ≥ 127 from by omega, ↓reduceIte]
    calc (w : ℚ) * 2^(be - 152)
        < 2^26 * 2^(be - 152) := mul_lt_mul_of_pos_right hw (by positivity)
      _ = 2^(be + 1 - 127) := by rw [← pow_add]; congr 1; omega
  · push_neg at hge152
    simp only [show ¬((be : Int) - 152 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((be : Int) - 152)).toNat = 152 - be := by omega
    rw [htonat]
    unfold F32.threshQ
    by_cases hge126 : be + 1 ≥ 127
    · simp only [show be + 1 ≥ 127 from hge126, ↓reduceIte]
      rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(152 - be))]
      calc (w : ℚ) < 2^26 := hw
        _ = 2^(be + 1 - 127) * 2^(152 - be) := by rw [← pow_add]; congr 1; omega
    · push_neg at hge126
      simp only [show ¬(be + 1 ≥ 127) from by omega, ↓reduceIte]
      rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
      calc (w : ℚ) * 2^(127 - (be + 1))
          < 2^26 * 2^(127 - (be + 1)) := mul_lt_mul_of_pos_right hw (by positivity)
        _ = 2^(152 - be) := by rw [← pow_add]; congr 1; omega

/-! #### Step 1: biasedExp ≥ 1 -/

private theorem boundary_bexp_ge_one32 (x : F32) (hfin : x.isFinite) (_hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    x.biasedExp.val ≥ 1 := by
  by_contra hlt; push_neg at hlt
  have hbexp0 : x.biasedExp.val = 0 := by omega
  have hesig_lt := F32.esig_lt_23_sub x hbexp0
  have hebe : x.effectiveBinaryExp = -149 := by
    unfold F32.effectiveBinaryExp F32.expBias F32.mantBits; simp [hbexp0]
  have he2 : x.effectiveBinaryExp - 2 = -151 := by rw [hebe]; ring
  have ⟨_, habs_hi⟩ := interval_abs_bounds32 x hfin q hq_ne hdec hq
  simp only [he2, show ¬((-151 : Int) ≥ 0) from by omega, ↓reduceIte,
             show ((-(-151 : Int)).toNat) = 151 from by omega] at habs_hi
  have hesig_nat : x.effectiveSignificand < 2^23 := by exact_mod_cast hesig_lt
  have hw_bound : (4 * x.effectiveSignificand + 2 : ℚ) ≤ 2^25 - 2 := by
    have hle : (x.effectiveSignificand : ℤ) ≤ (2^23 : ℤ) - 1 := by omega
    have : (x.effectiveSignificand : ℚ) ≤ 2^23 - 1 := by exact_mod_cast hle
    linarith
  have hq_lt : |q| < F32.threshQ 1 := by
    unfold F32.threshQ; simp only [show ¬(1 ≥ 127) from by omega, ↓reduceIte,
                                   show 127 - 1 = 126 from by omega]
    calc |q| ≤ (↑(4 * x.effectiveSignificand + 2)) / 2^151 := habs_hi
      _ ≤ (2^25 - 2 : ℚ) / 2^151 :=
          div_le_div_of_nonneg_right (by exact_mod_cast (show (4 * x.effectiveSignificand + 2 : ℤ) ≤ (2^25 : ℤ) - 2 from by omega)) (by positivity)
      _ < 1 / 2^126 := by rw [div_lt_div_iff₀ (by positivity) (by positivity)]; norm_num
  have hfbe_zero : F32.findBiasedExp |q| = 0 := by
    unfold F32.findBiasedExp
    apply F32.go_eq
    · omega
    · left; rfl
    · intro e he hle; push_neg
      calc |q| < F32.threshQ 1 := hq_lt
        _ ≤ F32.threshQ e := F32.threshQ_le_of_le (by omega)
  rw [hfbe_zero, hbexp0] at hfbe_ne
  exact absurd rfl hfbe_ne

/-! #### Step 1b: mantissa = 0 -/

private theorem boundary_mant_zero32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    x.mantissa.val = 0 := by
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  by_contra hmant_ne
  have hesig := F32.esig_normal x (by omega : x.biasedExp.val ≠ 0)
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  have hebe := F32.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 152 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) = 2 := by
    simp [hmant_ne]
  -- u ≥ 2^25 + 2 > 2^25
  have hu_ge : 4 * x.effectiveSignificand - 2 ≥ 2^25 + 2 := by rw [hesig]; omega
  -- Get bounds
  have ⟨habs_lo, habs_hi⟩ := interval_abs_bounds32 x hfin q hq_ne hdec hq
  simp only [hdelta] at habs_lo
  rw [he2] at habs_lo habs_hi
  -- |q| ≥ threshQ(biasedExp)
  have hscaleN_ge := scaleN_ge_threshQ32 (4 * x.effectiveSignificand - 2) x.biasedExp.val
    (by omega) hbexp hexp_lt
  rw [show ((x.biasedExp.val : Int) - 152) = (x.biasedExp.val : Int) - 152 from rfl] at hscaleN_ge
  have hge_thresh : F32.threshQ x.biasedExp.val ≤ |q| := le_trans hscaleN_ge habs_lo
  -- |q| < threshQ(biasedExp + 1) using w < 2^26
  have hesig_lt := F32.esig_lt_24 x
  have hw_lt : (4 * x.effectiveSignificand + 2 : ℚ) < 2^26 := by
    have hesig_nat : x.effectiveSignificand < 2^24 := by exact_mod_cast hesig_lt
    have : (x.effectiveSignificand : ℚ) ≤ 2^24 - 1 := by
      exact_mod_cast (show (x.effectiveSignificand : ℤ) ≤ (2^24 : ℤ) - 1 from by omega)
    linarith
  have hlt_thresh := scaleN_lt_threshQ_succ32 (4 * x.effectiveSignificand + 2) x.biasedExp.val
    (by exact_mod_cast hw_lt) hbexp hexp_lt
  have hlt_thresh_q : |q| < F32.threshQ (x.biasedExp.val + 1) :=
    lt_of_le_of_lt habs_hi hlt_thresh
  -- findBiasedExp = biasedExp
  have hfbe : F32.findBiasedExp |q| = x.biasedExp.val := by
    unfold F32.findBiasedExp
    apply F32.go_eq
    · omega
    · right; exact hge_thresh
    · intro e hgt hle; push_neg
      calc |q| < F32.threshQ (x.biasedExp.val + 1) := hlt_thresh_q
        _ ≤ F32.threshQ e := F32.threshQ_le_of_le (by omega)
  exact absurd hfbe hfbe_ne

/-! #### Step 2: |q| < threshQ(biasedExp) -/

private theorem boundary_qabs_lt_thresh32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    |q| < F32.threshQ x.biasedExp.val := by
  by_contra hge; push_neg at hge
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^23 := by
    rw [F32.esig_normal x (by omega)]; simp [hmant]
  have hebe := F32.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 152 := by rw [hebe]; ring
  have ⟨_, habs_hi⟩ := interval_abs_bounds32 x hfin q hq_ne hdec hq
  rw [hesig_val, he2] at habs_hi
  -- w = 2^25 + 2 < 2^26
  have hw_lt : ((4 * (2:Nat)^23 + 2 : Nat) : ℚ) < 2^26 := by norm_num
  have hlt_thresh := scaleN_lt_threshQ_succ32 (4 * 2^23 + 2) x.biasedExp.val hw_lt hbexp hexp_lt
  have : |q| < F32.threshQ (x.biasedExp.val + 1) := lt_of_le_of_lt habs_hi hlt_thresh
  -- findBiasedExp = biasedExp
  have hfbe_eq : F32.findBiasedExp |q| = x.biasedExp.val := by
    unfold F32.findBiasedExp
    apply F32.go_eq
    · omega
    · right; exact hge
    · intro e hgt hle; push_neg
      calc |q| < F32.threshQ (x.biasedExp.val + 1) := this
        _ ≤ F32.threshQ e := F32.threshQ_le_of_le (by omega)
  exact absurd hfbe_eq hfbe_ne

/-! #### Step 2b: |q| ≥ threshQ(biasedExp - 1) -/

private theorem boundary_qabs_ge_prev32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    F32.threshQ (x.biasedExp.val - 1) ≤ |q| := by
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^23 := by
    rw [F32.esig_normal x (by omega)]; simp [hmant]
  have hebe := F32.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 152 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) =
      if x.biasedExp.val > 1 then 1 else 2 := by simp [hmant]
  have ⟨habs_lo, _⟩ := interval_abs_bounds32 x hfin q hq_ne hdec hq
  rw [hdelta, hesig_val, he2] at habs_lo
  apply le_trans _ habs_lo
  by_cases hbe1 : x.biasedExp.val = 1
  · have he2_val : (x.biasedExp.val : Int) - 152 = -151 := by omega
    rw [he2_val, hbe1]
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte,
               show (4 * (2:Nat)^23 - 2) = (2^25 - 2 : Nat) from by norm_num,
               show ¬((-151 : Int) ≥ 0) from by omega,
               show ((-(-151 : Int)).toNat) = 151 from by omega,
               show 1 - 1 = 0 from by omega]
    unfold F32.threshQ; simp only [show ¬(0 ≥ 127) from by omega, ↓reduceIte,
                                   show 127 - 0 = 127 from by omega]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    norm_num
  · have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    simp only [show x.biasedExp.val > 1 from by omega, ↓reduceIte,
               show (4 * (2:Nat)^23 - 1) = (2^25 - 1 : Nat) from by norm_num]
    by_cases hge152 : (x.biasedExp.val : Int) - 152 ≥ 0
    · simp only [if_pos hge152]
      have htonat : ((x.biasedExp.val : Int) - 152).toNat = x.biasedExp.val - 152 := by omega
      rw [htonat]
      unfold F32.threshQ; simp only [show x.biasedExp.val - 1 ≥ 127 from by omega, ↓reduceIte]
      calc (2:ℚ) ^ (x.biasedExp.val - 1 - 127)
          = 2^24 * 2^(x.biasedExp.val - 152) := by rw [← pow_add]; congr 1; omega
        _ ≤ ((2^25 - 1 : Nat) : ℚ) * 2^(x.biasedExp.val - 152) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    · push_neg at hge152
      simp only [show ¬((x.biasedExp.val : Int) - 152 ≥ 0) from by omega, ↓reduceIte]
      have htonat : (-((x.biasedExp.val : Int) - 152)).toNat = 152 - x.biasedExp.val := by omega
      rw [htonat]
      unfold F32.threshQ
      by_cases hge128 : x.biasedExp.val - 1 ≥ 127
      · simp only [show x.biasedExp.val - 1 ≥ 127 from hge128, ↓reduceIte]
        rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(152 - x.biasedExp.val))]
        calc (2:ℚ) ^ (x.biasedExp.val - 1 - 127) * 2^(152 - x.biasedExp.val)
            = 2^24 := by rw [← pow_add]; congr 1; omega
          _ ≤ ((2^25 - 1 : Nat) : ℚ) := by norm_num
      · push_neg at hge128
        simp only [show ¬(x.biasedExp.val - 1 ≥ 127) from by omega, ↓reduceIte]
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        calc (2:ℚ) ^ (152 - x.biasedExp.val)
            = 2^24 * 2^(127 - (x.biasedExp.val - 1)) := by rw [← pow_add]; congr 1; omega
          _ ≤ ((2^25 - 1 : Nat) : ℚ) * 2^(127 - (x.biasedExp.val - 1)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-! #### Step 2c: findBiasedExp = biasedExp - 1 -/

private theorem boundary_fbe_eq32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    F32.findBiasedExp |q| = x.biasedExp.val - 1 := by
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hqlt := boundary_qabs_lt_thresh32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hqge := boundary_qabs_ge_prev32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  unfold F32.findBiasedExp
  apply F32.go_eq
  · omega
  · by_cases hbe1 : x.biasedExp.val = 1
    · left; omega
    · right; exact hqge
  · intro e he hle; push_neg
    calc |q| < F32.threshQ x.biasedExp.val := hqlt
      _ ≤ F32.threshQ e := F32.threshQ_le_of_le (by omega)

/-! #### Step 3: roundSignificand(|q|, biasedExp - 1) = (0, true) -/

/-- If sigExact inside sigRoundedOf32 lies in [N - 1/2, N) with N ≥ 2 and (N-1) odd,
    then sigRoundedOf32 = N. -/
private theorem sigRoundedOf_eq_of_bounds32 (qAbs : ℚ) (bexp N : Nat)
    (hN_ge : N ≥ 2) (hN_odd_pred : (N - 1) % 2 = 1)
    (hlo : (N : ℚ) - 1/2 ≤
      let binExp : Int := if bexp = 0 then -149 else (bexp : Int) - 150
      if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
      else qAbs * (2 ^ (-binExp).toNat : ℚ))
    (hhi :
      (let binExp : Int := if bexp = 0 then -149 else (bexp : Int) - 150
      if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
      else qAbs * (2 ^ (-binExp).toNat : ℚ)) < N) :
    sigRoundedOf32 qAbs bexp = N := by
  unfold sigRoundedOf32
  simp only [] at hlo hhi ⊢
  exact round_to_N32 N _ hlo hhi hN_ge hN_odd_pred

/-- Convert interval lower bound to sigExact lower bound for bexp=1 (subnormal boundary).
    The interval gives (4·2^23-2)/2^151 ≤ |q|, and sigExact = |q|·2^149,
    so sigExact ≥ (4·2^23-2)/4 = 2^23 - 1/2. -/
private theorem boundary_sigExact_lo_sub32 (qAbs : ℚ)
    (habs_lo : ((4 * 2 ^ 23 - 2 : Nat) : ℚ) / 2 ^ 151 ≤ qAbs) :
    (2^23 : ℚ) - 1/2 ≤ qAbs * 2^149 := by
  have hscale : ((4 * 2^23 - 2 : Nat) : ℚ) / 2^151 * 2^149 = 2^23 - 1/2 := by
    have h1 : (2:ℚ)^151 = 2^2 * 2^149 := by rw [← pow_add]
    rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^149 ≠ 0)]
    push_cast; norm_num
  linarith [mul_le_mul_of_nonneg_right habs_lo (show (0:ℚ) ≤ 2^149 from by positivity)]

/-- Convert threshQ upper bound to sigExact upper bound for bexp=1.
    threshQ(1) = 1/2^126, sigExact = |q|·2^149, so sigExact < 2^23. -/
private theorem boundary_sigExact_hi_sub32 (qAbs : ℚ)
    (hqlt : qAbs < (1:ℚ) / 2^126) :
    qAbs * 2^149 < 2^23 := by
  have hscale : (1:ℚ) / 2^126 * 2^149 = 2^23 := by
    rw [one_div, inv_mul_eq_div]
    rw [show (2:ℚ)^149 = 2^23 * 2^126 from by rw [← pow_add]]
    rw [mul_div_cancel_right₀ _ (by positivity : (2:ℚ)^126 ≠ 0)]
  linarith [mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^149 from by positivity)]

/-- Convert interval lower bound to sigExact lower bound for bexp≥2 (normal boundary).
    In all sub-cases, the interval gives (2^25-1)·scale ≤ |q| and sigExact = |q|/scale',
    yielding sigExact ≥ (2^25-1)/2 = 2^24 - 1/2. -/
private theorem boundary_sigExact_lo_norm32 (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (habs_lo : (if (bexp : Int) - 152 ≥ 0
      then ((2^25 - 1 : Nat) : ℚ) * 2^((bexp : Int) - 152).toNat
      else ((2^25 - 1 : Nat) : ℚ) / 2^(-((bexp : Int) - 152)).toNat) ≤ qAbs) :
    (2^24 : ℚ) - 1/2 ≤
      (if ((bexp : Int) - 151 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 151).toNat : ℚ)
       else qAbs * (2 ^ (-((bexp : Int) - 151)).toNat : ℚ)) := by
  by_cases hbinexp_ge : (bexp : Int) - 151 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 151).toNat = bexp - 151 := by omega
    rw [htonat]
    by_cases hge152 : (bexp : Int) - 152 ≥ 0
    · simp only [if_pos hge152] at habs_lo
      have htonat2 : ((bexp : Int) - 152).toNat = bexp - 152 := by omega
      rw [htonat2] at habs_lo
      rw [le_div_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 151))]
      calc ((2:ℚ)^24 - 1/2) * 2^(bexp - 151)
          = ((2^25 - 1 : Nat) : ℚ) * 2^(bexp - 152) := by
            push_cast
            rw [show (2:ℚ)^(bexp - 151) = 2^1 * 2^(bexp - 152) from by
              rw [← pow_add]; congr 1; omega]
            ring
        _ ≤ qAbs := habs_lo
    · push_neg at hge152
      have hbe_eq : bexp = 151 := by omega
      simp only [show ¬((bexp : Int) - 152 ≥ 0) from by omega, ↓reduceIte] at habs_lo
      have htonat2 : (-((bexp : Int) - 152)).toNat = 152 - bexp := by omega
      rw [htonat2, hbe_eq] at habs_lo
      rw [hbe_eq, show 151 - 151 = 0 from by omega, pow_zero]
      simp only [div_one]
      have : ((2^25 - 1 : Nat) : ℚ) / 2 ^ 1 = 2^24 - 1/2 := by push_cast; norm_num
      linarith
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 151 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 151)).toNat = 151 - bexp := by omega
    rw [htonat]
    have he2_neg : ¬((bexp : Int) - 152 ≥ 0) := by omega
    simp only [he2_neg, ↓reduceIte] at habs_lo
    have htonat3 : (-((bexp : Int) - 152)).toNat = 152 - bexp := by omega
    rw [htonat3] at habs_lo
    have h := mul_le_mul_of_nonneg_right habs_lo (show (0:ℚ) ≤ 2^(151 - bexp) from by positivity)
    calc (2^24 : ℚ) - 1/2
        = ((2^25 - 1 : Nat) : ℚ) / 2^(152 - bexp) * 2^(151 - bexp) := by
          push_cast
          have h1 : (2:ℚ)^(152 - bexp) = 2^1 * 2^(151 - bexp) := by
            rw [← pow_add]; congr 1; omega
          rw [h1, ← div_div, div_mul_cancel₀ _ (by positivity : (2:ℚ)^(151 - bexp) ≠ 0)]
          norm_num
      _ ≤ qAbs * 2^(151 - bexp) := h

/-- Convert threshQ upper bound to sigExact upper bound for bexp≥2.
    In all sub-cases, threshQ(bexp)·(1/2^binExp) = 2^24, so sigExact < 2^24. -/
private theorem boundary_sigExact_hi_norm32 (bexp : Nat) (qAbs : ℚ) (hbexp : bexp ≥ 2)
    (hexp_lt : bexp < 255)
    (hqlt : qAbs < F32.threshQ bexp) :
    (if ((bexp : Int) - 151 ≥ 0) then qAbs / (2 ^ ((bexp : Int) - 151).toNat : ℚ)
     else qAbs * (2 ^ (-((bexp : Int) - 151)).toNat : ℚ)) < 2^24 := by
  by_cases hbinexp_ge : (bexp : Int) - 151 ≥ 0
  · simp only [if_pos hbinexp_ge]
    have htonat : ((bexp : Int) - 151).toNat = bexp - 151 := by omega
    rw [htonat]
    unfold F32.threshQ at hqlt
    simp only [show bexp ≥ 127 from by omega, ↓reduceIte] at hqlt
    rw [div_lt_iff₀ (by positivity : (0:ℚ) < 2^(bexp - 151))]
    calc qAbs < 2^(bexp - 127) := hqlt
      _ = 2^24 * 2^(bexp - 151) := by rw [← pow_add]; congr 1; omega
  · push_neg at hbinexp_ge
    simp only [show ¬((bexp : Int) - 151 ≥ 0) from by omega, ↓reduceIte]
    have htonat : (-((bexp : Int) - 151)).toNat = 151 - bexp := by omega
    rw [htonat]
    unfold F32.threshQ at hqlt
    by_cases hge127 : bexp ≥ 127
    · simp only [show bexp ≥ 127 from hge127, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(151 - bexp) from by positivity)
      calc qAbs * 2^(151 - bexp)
        _ < 2^(bexp - 127) * 2^(151 - bexp) := h
        _ = 2^24 := by rw [← pow_add]; congr 1; omega
    · push_neg at hge127
      simp only [show ¬(bexp ≥ 127) from by omega, ↓reduceIte] at hqlt
      have h := mul_lt_mul_of_pos_right hqlt (show (0:ℚ) < 2^(151 - bexp) from by positivity)
      calc qAbs * 2^(151 - bexp)
        _ < 1 / 2^(127 - bexp) * 2^(151 - bexp) := h
        _ = 2^24 := by
            rw [one_div, inv_mul_eq_div]
            rw [div_eq_iff (by positivity : (0:ℚ) < 2^(127 - bexp)).ne']
            rw [← pow_add]; congr 1; omega

private theorem boundary_roundSig32 (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (q : ℚ) (hq_ne : q ≠ 0) (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    F32.roundSignificand |q| (x.biasedExp.val - 1) = (0, true) := by
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hqlt := boundary_qabs_lt_thresh32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  have hesig_val : x.effectiveSignificand = 2^23 := by
    rw [F32.esig_normal x (by omega)]; simp [hmant]
  have hebe := F32.ebe_normal x (by omega : x.biasedExp.val ≠ 0)
  have he2 : x.effectiveBinaryExp - 2 = (x.biasedExp.val : Int) - 152 := by rw [hebe]; ring
  have hdelta : (if x.mantissa.val = 0 ∧ x.biasedExp.val > 1 then 1 else 2 : Nat) =
      if x.biasedExp.val > 1 then 1 else 2 := by simp [hmant]
  have ⟨habs_lo, _⟩ := interval_abs_bounds32 x hfin q hq_ne hdec hq
  rw [hdelta, hesig_val, he2] at habs_lo
  rw [roundSignificand_split32]
  by_cases hbe1 : x.biasedExp.val = 1
  · -- Case biasedExp = 1: roundSignificand(|q|, 0)
    simp only [hbe1, show 1 - 1 = 0 from by omega]
    suffices hsig : sigRoundedOf32 |q| 0 = 2^23 by
      rw [hsig]; unfold branchOf32; simp
    have he2_val : (x.biasedExp.val : Int) - 152 = -151 := by omega
    rw [he2_val, hbe1] at habs_lo
    simp only [show ¬((1:Nat) > 1) from by omega, ↓reduceIte,
               show ¬((-151 : Int) ≥ 0) from by omega,
               show ((-(-151 : Int)).toNat) = 151 from by omega] at habs_lo
    rw [hbe1] at hqlt; unfold F32.threshQ at hqlt
    simp only [show ¬(1 ≥ 127) from by omega, ↓reduceIte, show 127 - 1 = 126 from by omega] at hqlt
    exact sigRoundedOf_eq_of_bounds32 |q| 0 (2^23) (by norm_num) (by norm_num)
      (by simp only [↓reduceIte, show ¬((-149 : Int) ≥ 0) from by omega,
                      show ((-(-149 : Int)).toNat) = 149 from by omega]
          exact boundary_sigExact_lo_sub32 |q| habs_lo)
      (by simp only [↓reduceIte, show ¬((-149 : Int) ≥ 0) from by omega,
                      show ((-(-149 : Int)).toNat) = 149 from by omega]
          exact boundary_sigExact_hi_sub32 |q| hqlt)
  · -- Case biasedExp ≥ 2: roundSignificand(|q|, biasedExp-1)
    have hbe_ge2 : x.biasedExp.val ≥ 2 := by omega
    have hbm1_ne0 : x.biasedExp.val - 1 ≠ 0 := by omega
    suffices hsig : sigRoundedOf32 |q| (x.biasedExp.val - 1) = 2^24 by
      rw [hsig]; unfold branchOf32; simp only [hbm1_ne0, ↓reduceIte]; norm_num
    have hbinexp : ((x.biasedExp.val - 1 : Nat) : Int) - 150 = (x.biasedExp.val : Int) - 151 := by omega
    simp only [show x.biasedExp.val > 1 from by omega, ↓reduceIte,
               show (4 * (2:Nat)^23 - 1) = (2^25 - 1 : Nat) from by norm_num] at habs_lo
    exact sigRoundedOf_eq_of_bounds32 |q| (x.biasedExp.val - 1) (2^24) (by norm_num) (by norm_num)
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact boundary_sigExact_lo_norm32 x.biasedExp.val |q| hbe_ge2 habs_lo)
      (by simp only [hbm1_ne0, ↓reduceIte, hbinexp]
          exact boundary_sigExact_hi_norm32 x.biasedExp.val |q| hbe_ge2 hexp_lt hqlt)

/-! #### Step 4: Assembly -/

/-- Case B: boundary case where findBiasedExp returns bexp-1.
    This happens only when mantissa=0 and the interval lower bound
    crosses the exponent threshold. The bump mechanism in
    roundSignificand corrects the exponent back to bexp. -/
private theorem interval_round_boundary32 (x : F32) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q)
    (hfbe_ne : F32.findBiasedExp |q| ≠ x.biasedExp.val) :
    F32.roundToNearestEven q = x := by
  have hbexp := boundary_bexp_ge_one32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hmant := boundary_mant_zero32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hfbe := boundary_fbe_eq32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hrs := boundary_roundSig32 x hfin hne q hq_ne hdec hq hfbe_ne
  have hexp_lt := F32.finite_implies_exp_lt x hfin
  unfold F32.roundToNearestEven
  rw [if_neg hq_ne]
  simp only []
  rw [hfbe, hrs]
  simp only [ite_true]
  have hfinalExp : x.biasedExp.val - 1 + 1 = x.biasedExp.val := by omega
  rw [hfinalExp]
  have hlt_max : ¬(x.biasedExp.val ≥ F32.maxBiasedExp) := by unfold F32.maxBiasedExp; omega
  rw [if_neg hlt_max]
  unfold F32.mkFinite
  simp only [show x.biasedExp.val < 255 from hexp_lt, show (0:Nat) < 2^23 from by norm_num, dite_true]
  rw [hdec]
  rcases x with ⟨s, ⟨be, hbe_bound⟩, ⟨m, hm_bound⟩⟩
  rw [F32.mk.injEq]
  refine ⟨rfl, Fin.ext rfl, Fin.ext ?_⟩
  simp at hmant; exact hmant.symm

/-! ### Assembly -/

/-- Assembly: the acceptance interval is sound. -/
private theorem interval_round_core32 (x : F32) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0) (q : ℚ) (hq_ne : q ≠ 0)
    (hdec : decide (q < 0) = x.sign)
    (hq : (schubfachInterval32 x hfin).contains q) :
    F32.roundToNearestEven q = x := by
  by_cases hfbe : F32.findBiasedExp |q| = x.biasedExp.val
  · exact interval_round_same_exp32 x hfin hne q hq_ne hdec hq hfbe
  · exact interval_round_boundary32 x hfin hne q hq_ne hdec hq hfbe

/-- The acceptance interval is sound: any rational in the interval
    rounds to x. -/
theorem schubfach_interval_correct32 (x : F32) (hfin : x.isFinite)
    (hne : x.toRat ≠ 0)
    (q : ℚ) (hq : (schubfachInterval32 x hfin).contains q) :
    F32.roundToNearestEven q = x := by
  -- Step 1: q ≠ 0 (the interval for non-zero x doesn't contain 0)
  have hq_ne : q ≠ 0 := by
    intro heq; subst heq
    have ⟨hlo_pos, _⟩ := schubfach_abs_interval_pos32 x hfin hne
    unfold AcceptanceInterval.contains at hq
    cases hs : x.sign <;> simp [hs] at hlo_pos hq
    · obtain ⟨h, _⟩ := hq; split at h <;> linarith
    · obtain ⟨_, h⟩ := hq; split at h <;> linarith
  -- Step 2: sign of q matches x.sign
  have hdec : decide (q < 0) = x.sign := by
    have ⟨hlo_pos, _⟩ := schubfach_abs_interval_pos32 x hfin hne
    have hqc := hq
    unfold AcceptanceInterval.contains at hqc
    cases hs : x.sign <;> simp [hs] at hlo_pos hqc
    · obtain ⟨h, _⟩ := hqc
      have : 0 < q := by split at h <;> linarith
      exact decide_eq_false (by linarith)
    · obtain ⟨_, h⟩ := hqc
      have : q < 0 := by split at h <;> linarith
      exact decide_eq_true this
  exact interval_round_core32 x hfin hne q hq_ne hdec hq

end ShortestDecimal
