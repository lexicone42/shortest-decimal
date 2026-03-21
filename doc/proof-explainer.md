# ShortestDecimal: What This Proves (and Doesn't)

A precise explanation of what the generic roundtrip theorem guarantees, its scope, and its limitations.

## What is proven

### The main theorem

```lean
theorem generic_full_roundtrip (alg : DecimalConversionAlgorithm)
    (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (alg.convert x hfin))).map Decimal.toF64 = some x
```

**In plain English**: Take any finite IEEE 754 double-precision float `x`. Apply any algorithm `alg` that satisfies the `DecimalConversionAlgorithm` interface. The algorithm produces a `Decimal`. Format that decimal to a string. Parse the string back to a decimal. Convert the parsed decimal back to a float. You get `x` — the original float, exactly.

This holds for **all** 2047 × 2^53 finite IEEE 754 doubles, including:
- Positive and negative zero
- All subnormals (biasedExp = 0, mantissa ≠ 0)
- All normals (biasedExp 1..2046)
- Edge cases: smallest subnormal (5 × 10^-324), largest finite (1.8 × 10^308)

### What "satisfying the interface" means

An algorithm must prove four things:

1. **`well_formed`**: The output `Decimal` has no trailing zeros in its digits, and zero inputs produce zero digits. This ensures the format/parse step is lossless.

2. **`in_interval`**: For non-zero floats, the output's rational value lies in the *acceptance interval* — the set of rationals that round to `x` under IEEE 754 round-to-nearest-even. This is the core obligation.

3. **`zero_digits`**: For zero floats, the output has `digits = 0`.

4. **`zero_sign`**: For zero floats, the output preserves the sign (distinguishing +0 from -0).

### The three proof layers

**Layer 1: Acceptance interval soundness** (`schubfach_interval_correct`, ~1,100 lines)

The hardest proof. Establishes: for any finite non-zero F64 `x`, the Schubfach interval `[u·2^e₂, w·2^e₂]` is *sound* — every rational in it rounds to `x` under round-to-nearest-even.

The interval is:
- `u = 4·mf - δ` (lower bound), `w = 4·mf + 2` (upper bound)
- `mf` = effective significand (2^52 + mantissa for normals)
- `δ = 1` at exponent boundaries (mantissa=0, biasedExp>1), `δ = 2` otherwise
- `e₂ = effectiveBinaryExp - 2` (the -2 gives one extra bit for tie-breaking precision)
- Boundaries are inclusive when mantissa is even (round-to-nearest-even tie rule)

The proof handles two cases:
- **Case A** (same exponent): `findBiasedExp(|q|) = x.biasedExp`. The rational `q` has the same binary exponent as `x`, so rounding recovers `x`'s mantissa via `round_in_half_interval`.
- **Case B** (boundary exponent): `findBiasedExp(|q|) = x.biasedExp - 1`. This happens only when `mantissa = 0` and the interval lower bound crosses a binade threshold. The `roundSignificand` bump mechanism corrects the exponent back. This case is ~350 lines and is the most mathematically subtle part.

**Layer 2: String format/parse roundtrip** (`format_parse_roundtrip`, ~450 lines)

Completely independent of IEEE 754. Proves that formatting a well-formed `Decimal` to scientific notation and parsing it back gives the original:
```
parse(format(d)) = some d  for all well-formed Decimals
```

The proof uses an 8-layer inversion:
1. Single digit chars: `parseDigitChar(Char.ofNat(d + 48)) = some d`
2. Digit list accumulator commutativity
3. Parser base case (non-digit termination)
4. Single digit parsing with accumulator update
5. Full digit list inversion via strong induction
6. Natural number roundtrip: `parseNat(natToDigits(n)) = some n`
7. Integer roundtrip (handles minus sign)
8. Full format roundtrip (dispatches on digit count for decimal point placement)

**Layer 3: Generic composition** (`generic_full_roundtrip`, ~30 lines)

Composes Layers 1 and 2:
1. Invoke `format_parse_roundtrip` to eliminate the string layer
2. For non-zero: invoke `schubfach_interval_correct` with the algorithm's `in_interval` proof
3. For zero: reconstruct ±0 from the algorithm's sign guarantee

## What is NOT proven

### 1. No specific algorithm is instantiated here

This library proves the *generic* theorem. It does NOT contain:
- The Ryu algorithm's `findDigits` search procedure
- Dragonbox's computation strategy
- Any algorithm-specific code

For a concrete instantiation, see [ryu-lean4](https://github.com/lexicone42/ryu-lean4).

### 2. "Shortest" is not proven (and not needed)

The theorem says nothing about the output being *shortest*. An algorithm that always returns `x` itself as a (possibly 17-digit) decimal would satisfy the interface — it's in the interval, it's well-formed, it roundtrips.

"Shortest" comes in two flavors:
- **Scale-minimal**: the output is found at the coarsest decimal grid. Proven for Ryu in ryu-lean4 (`ryu_shortest`), but not part of this generic theorem.
- **Digit-minimal**: the output has the fewest significant digits of any decimal in the interval. Not proven for any algorithm. The 2026 Champagne Gareau & Lemire survey found "none of the implementations surveyed consistently produced the shortest possible strings."

### 3. All five IEEE 754 rounding modes are covered for F64

The library now supports all five standard rounding modes for F64:
- **Round-to-nearest-even (RNE)** — the default mode, used by most software
- **Round-toward-zero (RTZ)** — truncation
- **Round-ties-to-away (RNA)** — the "schoolbook" rounding rule
- **Round-toward-positive (RTP)** — ceiling
- **Round-toward-negative (RTN)** — floor

Each mode has its own acceptance interval construction and soundness proof, its own rounding function and involution proof, and its own generic roundtrip theorem. All are fully proven with zero sorrys.

Dragonbox supports 10+ rounding policies. Additional modes beyond the IEEE 754 standard five (e.g., ties-to-odd) would require new interval soundness proofs.

### 4. F64 and F32 are modeled

The library models two IEEE 754 formats:

**F64 (binary64)** — all five rounding modes:
- 1 sign bit, 11 exponent bits, 52 mantissa bits
- Biased exponent range: 0..2047
- Special values: ±∞ (biasedExp=2047, mantissa=0), NaN (biasedExp=2047, mantissa≠0)

**F32 (binary32)** — RNE only:
- 1 sign bit, 8 exponent bits, 23 mantissa bits
- Biased exponent range: 0..255
- Special values: ±∞ (biasedExp=255, mantissa=0), NaN (biasedExp=255, mantissa≠0)

Extending to binary128 (quad) or binary16 (half) would require new types and re-proving the interval soundness with different constants.

### 5. No connection to hardware or Rust/C implementations

`F64` is a pure Lean type, not connected to:
- Lean's native `Float` type
- Rust's `f64` or C's `double`
- Any hardware FPU

The proof applies to the *mathematical model*, which faithfully mirrors IEEE 754 binary64. The gap between model and implementation is the standard gap in formal verification — bridging it would require tools like [Aeneas](https://github.com/AeneasVerif/aeneas) (for Rust) or [CompCert](https://compcert.org/) (for C).

### 6. No `native_decide` — kernel-only proofs

All finite-case proofs (character comparisons for digits 0-9, sign characters) use `decide` rather than `native_decide`. This means the entire proof chain is checked by Lean's kernel alone — the compiler is NOT in the trust base.

## The trust base

The proof relies on:
1. **Lean 4's type theory kernel** — the core checker that validates all proofs
2. **Mathlib** — for rational number arithmetic (`ℚ`), floor/ceiling operations, positivity tactics
3. **The F64 model** — faithfully mirrors IEEE 754 binary64 by construction (dependent types enforce bit widths)

No `native_decide`. No external axioms. No `sorry`. No `partial` definitions. The trust base is minimal: the Lean kernel + Mathlib.

## References

- Adams, "Ryū: fast float-to-string conversion", PLDI 2018 ([DOI](https://dl.acm.org/doi/10.1145/3296979.3192369))
- Jeon, "Dragonbox: A New Floating-Point Binary-to-Decimal Conversion Algorithm", 2020 ([PDF](https://raw.githubusercontent.com/jk-jeon/dragonbox/master/other_files/Dragonbox.pdf))
- Giulietti, "The Schubfach way to render doubles", 2022 ([PDF](https://fmt.dev/papers/Schubfach4.pdf))
- Loitsch, "Printing floating-point numbers quickly and accurately with integers", PLDI 2010 ([PDF](https://www.cs.tufts.edu/~nr/cs257/archive/florian-loitsch/printf.pdf))
- Andrysco et al., "Printing floating-point numbers: a faster, always correct method", POPL 2016 ([PDF](https://cseweb.ucsd.edu/~lerner/papers/fp-printing-popl16.pdf))
- Champagne Gareau & Lemire, "How (Not) to Convert Binary Numbers to Decimal", 2026 ([arXiv](https://arxiv.org/html/2603.06581))
- Nadezhin, verify-todec: ACL2 verification of Schubfach lemmas ([GitHub](https://github.com/nadezhin/verify-todec))
- Boldo & Melquiond, Flocq: Floating-point formalization in Coq ([HAL](https://inria.hal.science/inria-00534854v2))
- Cox, "Floating-Point Printing", research!rsc ([blog](https://research.swtch.com/fp))
