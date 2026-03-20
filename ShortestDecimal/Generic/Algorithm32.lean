/-
  Generic/Algorithm32.lean

  The algorithm-independent interface for decimal conversion algorithms
  targeting IEEE 754 binary32 (single-precision) floats.

  Now uses the interval-based interface (matching the F64 version),
  since the interval soundness proof for F32 is complete.
-/
import ShortestDecimal.Interval.Interval32
import ShortestDecimal.Decimal.Decimal

/-- Convert a Decimal to F32 via rounding.
    For zero digits, construct the F32 directly (preserving sign).
    Mirrors Decimal.toF64 but for single-precision. -/
def Decimal.toF32 (d : Decimal) : F32 :=
  if d.digits = 0 then ⟨d.sign, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  else F32.roundToNearestEven d.toRat

namespace ShortestDecimal

/-- A decimal conversion algorithm for IEEE 754 single-precision floats.
    Uses the interval-based interface, matching the F64 version. -/
structure DecimalConversionAlgorithm32 where
  convert : (x : F32) → x.isFinite → Decimal
  well_formed : ∀ (x : F32) (hfin : x.isFinite), (convert x hfin).WellFormed
  in_interval : ∀ (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0),
    (schubfachInterval32 x hfin).contains (convert x hfin).toRat
  zero_digits : ∀ (x : F32) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).digits = 0
  zero_sign : ∀ (x : F32) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).sign = x.sign

end ShortestDecimal
