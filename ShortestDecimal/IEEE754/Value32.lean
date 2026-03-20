/-
  IEEE754/Value32.lean

  Mathematical interpretation of F32 values as rationals (ℚ).
  Uses Mathlib's rational numbers for exact arithmetic.

  Normal:    (-1)^s × (2^23 + m) × 2^(e - 150)
  Subnormal: (-1)^s × m × 2^(-149)
-/
import ShortestDecimal.IEEE754.Classify32
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace F32

/-- The unbiased exponent for a normal number. -/
def unbiasedExp (x : F32) : Int :=
  (x.biasedExp.val : Int) - expBias

/-- The effective significand.
    Normal: 2^23 + mantissa.  Subnormal: mantissa. -/
def effectiveSignificand (x : F32) : Nat :=
  if x.biasedExp.val = 0 then x.mantissa.val
  else 2^mantBits + x.mantissa.val

/-- The effective binary exponent (accounting for implicit 2^23).
    Normal: biasedExp - 150.  Subnormal: -149. -/
def effectiveBinaryExp (x : F32) : Int :=
  if x.biasedExp.val = 0 then 1 - (expBias : Int) - mantBits
  else (x.biasedExp.val : Int) - expBias - mantBits

/-- The mathematical value of a finite F32 as a rational.
    value = (-1)^sign × significand × 2^binaryExp -/
def toRat (x : F32) : ℚ :=
  if ¬x.isFinite then 0
  else
    let sig : ℚ := x.effectiveSignificand
    let exp := x.effectiveBinaryExp
    let signMul : ℚ := if x.sign then -1 else 1
    if exp ≥ 0 then
      signMul * sig * (2 ^ exp.toNat : ℚ)
    else
      signMul * sig / (2 ^ (-exp).toNat : ℚ)

/-- Zero has rational value 0. -/
@[simp] theorem toRat_posZero : posZero.toRat = 0 := by
  simp [toRat, posZero, isFinite, classify, effectiveSignificand,
        effectiveBinaryExp, expBias, mantBits]

/-- Negative zero also has rational value 0. -/
@[simp] theorem toRat_negZero : negZero.toRat = 0 := by
  simp [toRat, negZero, isFinite, classify, effectiveSignificand,
        effectiveBinaryExp, expBias, mantBits]

end F32
