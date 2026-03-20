/-
  IEEE754/RoundToNearest32.lean

  Round-to-nearest-even: given a rational q, find the closest F32 value.
  On ties, pick the one with even mantissa LSB.
-/
import ShortestDecimal.IEEE754.Value32
import Mathlib.Data.Rat.Floor

namespace F32

/-- Construct a finite F32, returning none on overflow. -/
def mkFinite (s : Bool) (bexp : Nat) (mant : Nat) : Option F32 :=
  if h1 : bexp < 255 then
    if h2 : mant < 2^23 then
      some ⟨s, ⟨bexp, by omega⟩, ⟨mant, h2⟩⟩
    else none
  else none

/-- Find the biased exponent for a non-negative rational.
    Specification-level: iterate downward from 254. -/
def findBiasedExp (qAbs : ℚ) : Nat :=
  let rec go (e : Nat) : Nat :=
    if e = 0 then 0
    else
      let threshold : ℚ :=
        if e ≥ 127 then (2 ^ (e - 127) : ℚ)
        else 1 / (2 ^ (127 - e) : ℚ)
      if threshold ≤ qAbs then e
      else go (e - 1)
  termination_by e
  go 254

/-- Round a non-negative rational to the nearest significand
    for a given biased exponent, with round-to-nearest-even.
    Returns (mantissa, bumpExponent). -/
def roundSignificand (qAbs : ℚ) (bexp : Nat) : Nat × Bool :=
  let binExp : Int :=
    if bexp = 0 then -149
    else (bexp : Int) - 150
  -- Scale q to the significand: sigExact = qAbs / 2^binExp
  let sigExact : ℚ :=
    if binExp ≥ 0 then qAbs / (2 ^ binExp.toNat : ℚ)
    else qAbs * (2 ^ (-binExp).toNat : ℚ)
  let sigFloor := sigExact.floor.toNat
  let remainder := sigExact - sigFloor
  let sigRounded :=
    if remainder < 1/2 then sigFloor
    else if remainder > 1/2 then sigFloor + 1
    else if sigFloor % 2 = 0 then sigFloor else sigFloor + 1
  let (mant, bumpExp) :=
    if bexp = 0 then
      if sigRounded ≥ 2^23 then (sigRounded - 2^23, true)
      else (sigRounded, false)
    else
      if sigRounded ≥ 2 * 2^23 then (sigRounded / 2 - 2^23, true)
      else if sigRounded < 2^23 then (sigRounded, false)
      else (sigRounded - 2^23, false)
  (mant, bumpExp)

/-- Round-to-nearest-even: map a rational to the closest F32 value. -/
def roundToNearestEven (q : ℚ) : F32 :=
  if q = 0 then posZero
  else
    let s := q < 0
    let qAbs := |q|
    let bexp := findBiasedExp qAbs
    let (mant, bump) := roundSignificand qAbs bexp
    let finalExp := if bump then bexp + 1 else bexp
    if finalExp ≥ maxBiasedExp then
      if s then negInf else posInf
    else
      match mkFinite s finalExp mant with
      | some x => x
      | none => if s then negInf else posInf

end F32
