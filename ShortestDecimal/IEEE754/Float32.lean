/-
  IEEE754/Float32.lean

  IEEE 754 single-precision floating-point model.
  An F32 is decomposed into sign (1 bit), biased exponent (8 bits),
  and mantissa/significand (23 bits).

  Encoding (32 bits total):
    [31]     sign
    [30:23]  biased exponent (0..255)
    [22:0]   mantissa

  Special values:
    exponent = 0,   mantissa = 0  → ±0
    exponent = 0,   mantissa ≠ 0  → subnormal
    exponent = 255, mantissa = 0  → ±∞
    exponent = 255, mantissa ≠ 0  → NaN
    otherwise                     → normal: (-1)^s × 2^(e-127) × (1 + m/2^23)
-/

/-- IEEE 754 binary32 (single precision) floating-point number. -/
structure F32 where
  sign : Bool
  biasedExp : Fin 256    -- 8-bit biased exponent (0..255)
  mantissa : Fin (2^23)  -- 23-bit mantissa (0..2^23-1)
  deriving Repr, BEq, DecidableEq

namespace F32

-- IEEE 754 constants
def expBias : Nat := 127
def expBits : Nat := 8
def mantBits : Nat := 23
def maxBiasedExp : Nat := 255  -- 2^8 - 1

/-- Positive zero -/
def posZero : F32 := ⟨false, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Negative zero -/
def negZero : F32 := ⟨true, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Positive infinity -/
def posInf : F32 := ⟨false, ⟨255, by omega⟩, ⟨0, by omega⟩⟩

/-- Negative infinity -/
def negInf : F32 := ⟨true, ⟨255, by omega⟩, ⟨0, by omega⟩⟩

end F32
