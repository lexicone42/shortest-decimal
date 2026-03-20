/-
  Generic/Algorithm.lean

  The algorithm-independent interface for decimal conversion algorithms.

  Any algorithm that converts IEEE 754 floats to decimal strings must:
  1. Produce a well-formed Decimal for every finite float
  2. Ensure the Decimal's rational value lies in the acceptance interval
  3. Handle zero correctly

  The roundtrip theorem then follows automatically from the interval
  soundness proof (schubfach_interval_correct) and the format/parse
  roundtrip (format_parse_roundtrip).

  This covers: Ryu, Dragonbox/zmij, Schubfach, Grisu-Exact, Errol,
  and any future algorithm satisfying the interface.

  References:
  - Adams, "Ryū: fast float-to-string conversion", PLDI 2018
  - Jeon, "Dragonbox: A New Floating-Point Binary-to-Decimal Conversion Algorithm", 2020
  - Giulietti, "The Schubfach way to render doubles", 2022
  - Loitsch, "Printing floating-point numbers quickly and accurately with integers", PLDI 2010
  - Andrysco et al., "Printing floating-point numbers: a faster, always correct method", POPL 2016
  - Champagne Gareau & Lemire, "How (Not) to Convert Binary Numbers to Decimal", arXiv 2603.06581, 2026
-/
import ShortestDecimal.Interval.Interval
import ShortestDecimal.Roundtrip.FormatParse

namespace ShortestDecimal

/-- A decimal conversion algorithm: any function that converts finite
    IEEE 754 doubles to well-formed Decimals in the acceptance interval.

    The interface is minimal — it requires only what's needed for
    the roundtrip theorem. "Shortest" is a quality property, not a
    correctness property, so it is NOT required.

    Known algorithms satisfying this interface:
    - Ryu (Adams 2018): scale-minimal search
    - Dragonbox/zmij (Jeon 2020): digit-minimal with configurable tie-breaking
    - Schubfach (Giulietti 2022): pigeonhole-based search
    - Grisu-Exact (Jeon 2020): 128-bit Grisu variant
    - Errol (Andrysco et al. 2016): double-double arithmetic -/
structure DecimalConversionAlgorithm where
  /-- The algorithm: given a finite F64, produce a Decimal. -/
  convert : (x : F64) → x.isFinite → Decimal
  /-- The output is well-formed (no trailing zeros; zero digits → zero exponent). -/
  well_formed : ∀ (x : F64) (hfin : x.isFinite), (convert x hfin).WellFormed
  /-- For non-zero floats, the output's rational value is in the acceptance interval.
      This is the core obligation: it says the Decimal represents a value that
      rounds back to x under round-to-nearest-even. -/
  in_interval : ∀ (x : F64) (hfin : x.isFinite) (hne : x.toRat ≠ 0),
    (ShortestDecimal.schubfachInterval x hfin).contains (convert x hfin).toRat
  /-- For zero floats, the output has zero digits and matching sign. -/
  zero_digits : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).digits = 0
  zero_sign : ∀ (x : F64) (hfin : x.isFinite) (h0 : x.toRat = 0),
    (convert x hfin).sign = x.sign

end ShortestDecimal
