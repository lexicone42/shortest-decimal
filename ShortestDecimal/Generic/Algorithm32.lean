/-
  Generic/Algorithm32.lean

  The algorithm-independent interface for decimal conversion algorithms
  targeting IEEE 754 binary32 (single-precision) floats.

  Mirror of Algorithm.lean for F64, adapted for F32.
  Since the interval soundness proof for F32 is not yet available,
  the core obligation is stated directly in terms of roundToNearestEven:
  the algorithm's output must round back to the original F32 value.
-/
import ShortestDecimal.IEEE754.RoundProof32
import ShortestDecimal.Decimal.Decimal

namespace ShortestDecimal

/-- A decimal conversion algorithm for IEEE 754 single-precision floats.

    The interface mirrors DecimalConversionAlgorithm (for F64) but uses
    F32 types and states the roundtrip obligation directly via
    F32.roundToNearestEven, since the interval soundness proof for F32
    is deferred. -/
structure DecimalConversionAlgorithm32 where
  /-- The algorithm: given a finite F32, produce a Decimal. -/
  convert : (x : F32) → x.isFinite → Decimal
  /-- The output is well-formed (no trailing zeros; zero digits → zero exponent). -/
  well_formed : ∀ (x : F32) (hfin : x.isFinite), (convert x hfin).WellFormed
  /-- For non-zero floats, the output's rational value rounds back to x.
      This is the core obligation: it says the Decimal represents a value that
      rounds back to x under round-to-nearest-even. -/
  roundtrip : ∀ (x : F32) (hfin : x.isFinite) (hne : x.toRat ≠ 0),
    F32.roundToNearestEven (convert x hfin).toRat = x
  /-- For zero floats, the output has zero digits and matching sign. -/
  zero_digits : ∀ (x : F32) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).digits = 0
  zero_sign : ∀ (x : F32) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).sign = x.sign

end ShortestDecimal
