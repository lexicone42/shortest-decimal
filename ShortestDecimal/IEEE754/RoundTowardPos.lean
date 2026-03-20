/-
  IEEE754/RoundTowardPos.lean

  Round-toward-positive-infinity (RTP, ceiling): given a rational q,
  find the smallest F64 value ≥ q. For positive q this rounds up
  (ceiling of significand). For negative q this truncates toward zero
  (floor of significand magnitude). No tie-breaking is needed.
-/
import ShortestDecimal.IEEE754.RoundToNearest
import ShortestDecimal.IEEE754.RoundTowardZero
import Mathlib.Data.Rat.Floor

namespace F64

/-- Round a non-negative rational to the significand for a given biased
    exponent, using ceiling (round up).
    Returns (mantissa, bumpExponent). -/
def roundSignificand_rtp_up (qAbs : ℚ) (bexp : Nat) : Nat × Bool :=
  let binExp : Int :=
    if bexp = 0 then -1074
    else (bexp : Int) - 1075
  let sigExact : ℚ :=
    if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
    else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  -- Ceiling: round up if any fractional part
  let sigRounded := if remainder > 0 then sigFloor + 1 else sigFloor
  let (mant, bumpExp) :=
    if bexp = 0 then
      if sigRounded ≥ 2^52 then (sigRounded - 2^52, true)
      else (sigRounded, false)
    else
      if sigRounded ≥ 2 * 2^52 then (sigRounded / 2 - 2^52, true)
      else if sigRounded < 2^52 then (sigRounded, false)
      else (sigRounded - 2^52, false)
  (mant, bumpExp)

/-- Round-toward-positive-infinity: map a rational to the smallest F64 ≥ q.
    For positive q: ceiling (round up the significand).
    For negative q: truncation (floor of magnitude = round toward zero). -/
def roundTowardPos (q : ℚ) : F64 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    -- For positive q: ceiling. For negative q: floor (truncation toward zero).
    let (mant, bump) :=
      if s then roundSignificand_rtz qAbs bexp
      else roundSignificand_rtp_up qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

end F64
