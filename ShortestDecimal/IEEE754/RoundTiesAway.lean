/-
  IEEE754/RoundTiesAway.lean

  Round-to-nearest-ties-to-away (RNA): given a rational q, find the closest F64.
  On ties (exact midpoints), round AWAY from zero (i.e., toward larger magnitude).
  This is the opposite of RNE which rounds to even on ties.
-/
import ShortestDecimal.IEEE754.RoundToNearest
import Mathlib.Data.Rat.Floor

namespace F64

/-- Round a non-negative rational to the nearest significand
    for a given biased exponent, with round-to-nearest-ties-to-away.
    On ties (remainder = 1/2), always rounds up (away from zero).
    Returns (mantissa, bumpExponent). -/
def roundSignificand_rna (qAbs : ℚ) (bexp : Nat) : Nat × Bool :=
  let binExp : Int :=
    if bexp = 0 then -1074
    else (bexp : Int) - 1075
  let sigExact : ℚ :=
    if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
    else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  -- RNA: on ties (remainder = 1/2), round up (away from zero)
  let sigRounded :=
    if remainder < 1/2 then sigFloor
    else sigFloor + 1  -- ties and above both round up
  let (mant, bumpExp) :=
    if bexp = 0 then
      if sigRounded ≥ 2^52 then (sigRounded - 2^52, true)
      else (sigRounded, false)
    else
      if sigRounded ≥ 2 * 2^52 then (sigRounded / 2 - 2^52, true)
      else if sigRounded < 2^52 then (sigRounded, false)
      else (sigRounded - 2^52, false)
  (mant, bumpExp)

/-- Round-to-nearest-ties-to-away: map a rational to the closest F64 value.
    On ties, picks the value with larger magnitude (away from zero). -/
def roundTiesAway (q : ℚ) : F64 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    let (mant, bump) := roundSignificand_rna qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

end F64
