/-
  Examples/RyuInstance.lean

  How to instantiate DecimalConversionAlgorithm for the Ryu algorithm.
  The commented section shows the exact code pattern for ryu-lean4.
  The real section demonstrates what theorems you get for free once
  you have an algorithm satisfying the interface.
-/
import ShortestDecimal.Generic.Roundtrip

-- ============================================================
-- COMMENTED EXAMPLE: Instantiating for Ryu
-- ============================================================
--
-- In a project that depends on both shortest-decimal and ryu-lean4:
--
-- import ShortestDecimal
-- import RyuLean4
--
-- def ryuAlgorithm : ShortestDecimal.DecimalConversionAlgorithm where
--   convert := Ryu.ryu
--   well_formed := Ryu.ryu_well_formed
--   in_interval := Ryu.ryu_in_interval
--   zero_digits := fun x hfin h0 => by
--     unfold Ryu.ryu Ryu.shortestDecimal; simp [h0]
--   zero_sign := fun x hfin h0 => by
--     unfold Ryu.ryu Ryu.shortestDecimal; simp [h0]
--
-- -- The roundtrip follows automatically:
-- theorem ryu_roundtrip (x : F64) (hfin : x.isFinite) :
--     (Decimal.parse (Decimal.format (Ryu.ryu x hfin))).map Decimal.toF64 = some x :=
--   ShortestDecimal.generic_full_roundtrip ryuAlgorithm x hfin

-- ============================================================
-- REAL EXAMPLE: What you get from any DecimalConversionAlgorithm
-- ============================================================

namespace ShortestDecimal.Examples

/-- Given any algorithm satisfying the interface, the full string roundtrip holds:
    parse(format(alg(x))).map toF64 = some x -/
example (alg : DecimalConversionAlgorithm) (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (alg.convert x hfin))).map Decimal.toF64 = some x :=
  generic_full_roundtrip alg x hfin

/-- Given any algorithm satisfying the interface, the direct decimal roundtrip holds:
    alg(x).toF64 = x -/
example (alg : DecimalConversionAlgorithm) (x : F64) (hfin : x.isFinite) :
    (alg.convert x hfin).toF64 = x :=
  generic_decimal_roundtrip alg x hfin

/-- The algorithm's output is always well-formed (no trailing zeros). -/
example (alg : DecimalConversionAlgorithm) (x : F64) (hfin : x.isFinite) :
    (alg.convert x hfin).WellFormed :=
  alg.well_formed x hfin

/-- For zero floats, the algorithm preserves the sign bit. -/
example (alg : DecimalConversionAlgorithm) (x : F64) (hfin : x.isFinite)
    (h0 : x.toRat = 0) :
    (alg.convert x hfin).sign = x.sign :=
  alg.zero_sign x hfin h0

end ShortestDecimal.Examples
