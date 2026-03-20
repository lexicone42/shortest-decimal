/-
  Generic/AlgorithmRTP.lean

  The algorithm-independent interface for decimal conversion under RTP rounding.
-/
import ShortestDecimal.Interval.IntervalRTP
import ShortestDecimal.Roundtrip.FormatParse

namespace ShortestDecimal

/-- A decimal conversion algorithm for round-toward-positive-infinity. -/
structure DecimalConversionAlgorithmRTP where
  convert : (x : F64) → x.isFinite → Decimal
  well_formed : ∀ (x : F64) (hfin : x.isFinite), (convert x hfin).WellFormed
  in_interval : ∀ (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0),
    (ShortestDecimal.rtpInterval x hfin).contains (convert x hfin).toRat
  zero_digits : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).digits = 0
  zero_sign : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).sign = x.sign

end ShortestDecimal
