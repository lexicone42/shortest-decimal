/-
  IEEE754/RoundTowardNeg.lean

  Round-toward-negative-infinity (RTN, floor): given a rational q,
  find the largest F64 value ≤ q. For positive q this truncates
  (floor of significand). For negative q this rounds up the magnitude
  (ceiling of significand magnitude). No tie-breaking is needed.
-/
import ShortestDecimal.IEEE754.RoundToNearest
import ShortestDecimal.IEEE754.RoundTowardZero
import ShortestDecimal.IEEE754.RoundTowardPos
import Mathlib.Data.Rat.Floor

namespace F64

/-- Round-toward-negative-infinity: map a rational to the largest F64 ≤ q.
    For positive q: floor (truncation toward zero = floor of significand).
    For negative q: ceiling of magnitude (round away from zero). -/
def roundTowardNeg (q : ℚ) : F64 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    -- For positive q: floor (truncation). For negative q: ceiling (round up magnitude).
    let (mant, bump) :=
      if s then roundSignificand_rtp_up qAbs bexp
      else roundSignificand_rtz qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

end F64
