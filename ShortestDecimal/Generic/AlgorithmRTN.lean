/-
  Generic/AlgorithmRTN.lean

  The algorithm-independent interface for decimal conversion under RTN rounding.
-/
import ShortestDecimal.Interval.IntervalRTN
import ShortestDecimal.Roundtrip.FormatParse

namespace ShortestDecimal

/-- A decimal conversion algorithm for round-toward-negative-infinity. -/
structure DecimalConversionAlgorithmRTN where
  convert : (x : F64) → x.isFinite → Decimal
  well_formed : ∀ (x : F64) (hfin : x.isFinite), (convert x hfin).WellFormed
  in_interval : ∀ (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0),
    (ShortestDecimal.rtnInterval x hfin).contains (convert x hfin).toRat
  zero_digits : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).digits = 0
  zero_sign : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).sign = x.sign

end ShortestDecimal
