# ShortestDecimal

A generic, formally verified roundtrip theorem for IEEE 754 float-to-decimal conversion algorithms in Lean 4.

**The main theorem**: For ANY algorithm that produces a decimal in the acceptance interval, the roundtrip holds:

```lean
theorem generic_full_roundtrip (alg : DecimalConversionAlgorithm)
    (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (alg.convert x hfin))).map Decimal.toF64 = some x
```

This covers **all** algorithms in the Schubfach/shortest-decimal family:
- [Ryu](https://dl.acm.org/doi/10.1145/3296979.3192369) (Adams, PLDI 2018)
- [Dragonbox/zmij](https://github.com/jk-jeon/dragonbox) (Jeon, 2020)
- [Schubfach](https://fmt.dev/papers/Schubfach4.pdf) (Giulietti, 2022)
- [Grisu-Exact](https://github.com/jk-jeon/Grisu-Exact) (Jeon, 2020)
- [Errol](https://cseweb.ucsd.edu/~lerner/papers/fp-printing-popl16.pdf) (Andrysco et al., POPL 2016)
- Any future algorithm satisfying the interface

Zero `sorry`s. Zero axioms. All proofs checked by Lean's kernel.

## The key insight

**"Shortest" is irrelevant for correctness.** The roundtrip property only requires:

1. The algorithm produces a decimal whose rational value is in the **acceptance interval** — the set of rationals that round to the input float
2. The decimal is **well-formed** (no trailing zeros)

The acceptance interval soundness (`schubfach_interval_correct`, ~1,100 lines) proves that ANY rational in the interval rounds back to the original float. The format/parse roundtrip (`format_parse_roundtrip`, ~450 lines) proves that string formatting is lossless. The generic theorem composes these two facts — the algorithm-specific search procedure is abstracted away.

"Shortest" (whether scale-minimal or digit-minimal) is a **quality** property affecting human readability, not a correctness property. All algorithms listed above are correct; they differ in search strategy, tie-breaking, and optimality guarantees.

## The algorithm interface

```lean
structure DecimalConversionAlgorithm where
  convert : (x : F64) → x.isFinite → Decimal
  well_formed : ∀ x hfin, (convert x hfin).WellFormed
  in_interval : ∀ x hfin, x.toRat ≠ 0 →
    (schubfachInterval x hfin).contains (convert x hfin).toRat
  zero_digits : ∀ x hfin, x.toRat = 0 → (convert x hfin).digits = 0
  zero_sign : ∀ x hfin, x.toRat = 0 → (convert x hfin).sign = x.sign
```

To verify a new algorithm, provide these five obligations. The roundtrip theorem follows automatically.

## Project structure

```
ShortestDecimal/
├── IEEE754/                    # IEEE 754 binary64 model
│   ├── Float64.lean            # F64 structure (sign, biasedExp, mantissa)
│   ├── Classify.lean           # Float classification
│   ├── Value.lean              # F64 → ℚ rational interpretation
│   ├── RoundToNearest.lean     # ℚ → F64 rounding
│   └── RoundProof.lean         # RNE(toRat(x)) = x (involution)
├── Decimal/                    # Decimal representation
│   ├── Decimal.lean            # Decimal type + toRat/toF64
│   ├── Format.lean             # Decimal → String (scientific notation)
│   └── Parse.lean              # String → Decimal parser
├── Interval/                   # Acceptance interval
│   └── Interval.lean           # Construction + soundness (~1,100 lines)
├── Roundtrip/                  # String roundtrip
│   └── FormatParse.lean        # parse(format(d)) = d (~450 lines)
└── Generic/                    # Algorithm-independent interface
    ├── Algorithm.lean           # DecimalConversionAlgorithm structure
    └── Roundtrip.lean           # generic_full_roundtrip theorem
```

## Building

Requires [Lean 4](https://lean-lang.org/) and [Mathlib4](https://github.com/leanprover-community/mathlib4).

```bash
lake build    # ~20 min first build (fetches Mathlib)
```

## How to verify a new algorithm

1. Define your algorithm as a Lean function: `myAlg : (x : F64) → x.isFinite → Decimal`
2. Prove well-formedness: the output has no trailing zeros
3. Prove interval membership: for non-zero x, the output's `toRat` is in `schubfachInterval x hfin`
4. Handle zero: output has `digits = 0` and matching sign
5. Instantiate `DecimalConversionAlgorithm` and get the roundtrip theorem for free

See [ryu-lean4](https://github.com/lexicone42/ryu-lean4) for a concrete example.

## Proof architecture

The roundtrip proof decomposes into three independent layers:

```
Layer 1: Acceptance Interval Soundness (schubfach_interval_correct)
  "Any rational in [u·2^e₂, w·2^e₂] rounds to x under RNE"
  ~1,100 lines. The hardest proof. Algorithm-independent.

Layer 2: String Format/Parse Roundtrip (format_parse_roundtrip)
  "parse(format(d)) = d for well-formed Decimals"
  ~450 lines. 8-layer proof. Completely independent of IEEE 754.

Layer 3: Generic Composition (generic_full_roundtrip)
  "in_interval + well_formed → roundtrip"
  ~30 lines. Composes Layer 1 and Layer 2.
```

The generic theorem is 30 lines because all the hard work is in the layers.

## Related work

- [ryu-lean4](https://github.com/lexicone42/ryu-lean4) — Verified Ryu algorithm instantiation (~3,230 lines). Proves the Ryu-specific search (`findDigits`) produces output in the acceptance interval.
- [nickelean](https://github.com/lexicone42/nickelean) — Verified JSON serialization for Nickel, using this library + ryu-lean4.
- [Nadezhin verify-todec](https://github.com/nadezhin/verify-todec) — Partial ACL2 verification of Schubfach's mathematical lemmas (precision sufficiency).
- [Flocq](https://inria.hal.science/inria-00534854v2) — Coq library for floating-point arithmetic (Boldo, Melquiond). Formalizes rounding but not decimal conversion.

## References

- Adams, "Ryū: fast float-to-string conversion", PLDI 2018 ([paper](https://dl.acm.org/doi/10.1145/3296979.3192369))
- Jeon, "Dragonbox: A New Floating-Point Binary-to-Decimal Conversion Algorithm", 2020 ([paper](https://raw.githubusercontent.com/jk-jeon/dragonbox/master/other_files/Dragonbox.pdf))
- Giulietti, "The Schubfach way to render doubles", 2022 ([paper](https://fmt.dev/papers/Schubfach4.pdf))
- Loitsch, "Printing floating-point numbers quickly and accurately with integers", PLDI 2010 ([paper](https://www.cs.tufts.edu/~nr/cs257/archive/florian-loitsch/printf.pdf))
- Andrysco et al., "Printing floating-point numbers: a faster, always correct method", POPL 2016 ([paper](https://cseweb.ucsd.edu/~lerner/papers/fp-printing-popl16.pdf))
- Champagne Gareau & Lemire, "How (Not) to Convert Binary Numbers to Decimal", 2026 ([arXiv](https://arxiv.org/html/2603.06581))

## License

MIT
