/-
  Interval/CeilHelper.lean

  Shared ceiling infrastructure for RTP and RTN interval proofs.
-/
import ShortestDecimal.IEEE754.RoundProofRTP
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

/-! ## Ceiling lemma -/

/-- Ceiling in (n-1, n]: the ceiling operation gives n.
    This is the core lemma for both RTP (positive case) and RTN (negative case). -/
theorem ceil_in_interval (n : ℕ) (hn : n ≥ 1) (sigExact : ℚ)
    (hlo : (n : ℚ) - 1 < sigExact) (hhi : sigExact ≤ (n : ℚ)) :
    (let sigFloor := sigExact.floor.toNat
     let remainder := sigExact - ↑sigFloor
     if remainder > 0 then sigFloor + 1 else sigFloor) = n := by
  simp only []
  by_cases heq : sigExact = (n : ℚ)
  · -- sigExact = n: floor = n, remainder = 0, result = n
    subst heq
    have hfloor : ⌊(n : ℚ)⌋ = (n : ℤ) := Int.floor_natCast n
    have htonat : (n : ℚ).floor.toNat = n := by
      show ⌊(n : ℚ)⌋.toNat = n; rw [hfloor]; omega
    rw [htonat]
    have hrem : ¬((n : ℚ) - (n : ℚ) > 0) := by linarith [sub_self (n : ℚ)]
    rw [if_neg hrem]
  · -- sigExact ∈ (n-1, n): floor = n-1, remainder > 0, result = (n-1) + 1 = n
    have hlt : sigExact < (n : ℚ) := lt_of_le_of_ne hhi heq
    have hfloor : ⌊sigExact⌋ = (n : ℤ) - 1 := by
      rw [Int.floor_eq_iff]
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    have htonat : sigExact.floor.toNat = n - 1 := by
      show ⌊sigExact⌋.toNat = n - 1; rw [hfloor]; omega
    rw [htonat]
    have hn1_cast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      exact_mod_cast (show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 from by omega)
    have hrem_pos : sigExact - ((n - 1 : ℕ) : ℚ) > 0 := by rw [hn1_cast]; linarith
    rw [if_pos hrem_pos]; omega

/-! ## Decomposition of roundSignificand_rtp_up -/

/-- The ceiling of sigExact, matching roundSignificand_rtp_up's rounding step. -/
def sigCeilOf (qAbs : ℚ) (bexp : Nat) : Nat :=
  let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
  let sigExact : ℚ := if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
                       else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  if remainder > 0 then sigFloor + 1 else sigFloor

/-- The branch analysis after rounding, identical to RTZ/RNE. -/
def branchOfCeil (sigCeil : Nat) (bexp : Nat) : Nat × Bool :=
  if bexp = 0 then
    if sigCeil ≥ 2^52 then (sigCeil - 2^52, true) else (sigCeil, false)
  else
    if sigCeil ≥ 2 * 2^52 then (sigCeil / 2 - 2^52, true)
    else if sigCeil < 2^52 then (sigCeil, false)
    else (sigCeil - 2^52, false)

/-- roundSignificand_rtp_up factors through sigCeilOf and branchOfCeil. -/
theorem roundSignificand_rtp_up_split (qAbs : ℚ) (bexp : Nat) :
    F64.roundSignificand_rtp_up qAbs bexp = branchOfCeil (sigCeilOf qAbs bexp) bexp := rfl

/-- branchOfCeil(effectiveSignificand, biasedExp) = (mantissa, false). -/
theorem branchOfCeil_mf (x : F64) :
    branchOfCeil x.effectiveSignificand x.biasedExp.val = (x.mantissa.val, false) := by
  unfold branchOfCeil
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

/-- sigCeilOf matches effectiveSignificand when sigExact ∈ (mf-1, mf]. -/
theorem sigCeilOf_from_bounds (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0)
    (qAbs : ℚ)
    (hsig_lo : (x.effectiveSignificand : ℚ) - 1 <
      (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat))
    (hsig_hi : (if x.effectiveBinaryExp ≥ 0
       then qAbs / (2 : ℚ) ^ x.effectiveBinaryExp.toNat
       else qAbs * (2 : ℚ) ^ (-x.effectiveBinaryExp).toNat) ≤
      (x.effectiveSignificand : ℚ)) :
    sigCeilOf qAbs x.biasedExp.val = x.effectiveSignificand := by
  have hmf_pos : x.effectiveSignificand ≥ 1 := by
    by_contra h; push_neg at h
    have : x.effectiveSignificand = 0 := by omega
    exact hne (by unfold F64.toRat; rw [if_neg (not_not.mpr hfin)]; simp [this])
  unfold sigCeilOf; simp only []; rw [F64.binExp_eq]
  exact ceil_in_interval x.effectiveSignificand hmf_pos _ hsig_lo hsig_hi

/-- sigCeilOf = N when sigExact ∈ (N-1, N). -/
theorem sigCeilOf_eq_of_bounds (qAbs : ℚ) (bexp N : Nat) (hN : N ≥ 1)
    (hlo : (N : ℚ) - 1 <
      (let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
       if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
       else qAbs * (2 ^ (-binExp).toNat : ℚ)))
    (hhi : (let binExp : Int := if bexp = 0 then -1074 else (bexp : Int) - 1075
       if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
       else qAbs * (2 ^ (-binExp).toNat : ℚ)) < N) :
    sigCeilOf qAbs bexp = N := by
  unfold sigCeilOf; simp only [] at hlo hhi ⊢
  exact ceil_in_interval N hN _ hlo (le_of_lt hhi)

end ShortestDecimal
