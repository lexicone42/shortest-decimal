/-
  IEEE754/RoundTowardZero.lean

  Round-toward-zero (truncation): given a rational q, find the F64 value
  closest to zero. For positive q this is floor, for negative q this is
  ceiling. No tie-breaking is needed — truncation is deterministic.
-/
import ShortestDecimal.IEEE754.RoundToNearest
import Mathlib.Data.Rat.Floor

namespace F64

/-- Round a non-negative rational to the significand for a given biased
    exponent, using truncation (floor only — no tie-breaking).
    Returns (mantissa, bumpExponent). -/
def roundSignificand_rtz (qAbs : ℚ) (bexp : Nat) : Nat × Bool :=
  let binExp : Int :=
    if bexp = 0 then -1074
    else (bexp : Int) - 1075
  -- Scale q to the significand: sigExact = qAbs / 2^binExp
  let sigExact : ℚ :=
    if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
    else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let (mant, bumpExp) :=
    if bexp = 0 then
      if sigFloor ≥ 2^52 then (sigFloor - 2^52, true)
      else (sigFloor, false)
    else
      if sigFloor ≥ 2 * 2^52 then (sigFloor / 2 - 2^52, true)
      else if sigFloor < 2^52 then (sigFloor, false)
      else (sigFloor - 2^52, false)
  (mant, bumpExp)

/-- Round-toward-zero: map a rational to the F64 value nearest to zero.
    For positive q: floor (round down).
    For negative q: ceiling (round up toward zero). -/
def roundTowardZero (q : ℚ) : F64 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    let (mant, bump) := roundSignificand_rtz qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

end F64
