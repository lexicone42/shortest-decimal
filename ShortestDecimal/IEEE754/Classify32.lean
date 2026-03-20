/-
  IEEE754/Classify32.lean

  Classification of F32 values into zero, subnormal, normal, infinity, NaN.
-/
import ShortestDecimal.IEEE754.Float32
import ShortestDecimal.IEEE754.Classify

namespace F32

/-- Classify an F32 value. -/
def classify (x : F32) : FloatClass :=
  if x.biasedExp.val = 0 then
    if x.mantissa.val = 0 then .zero
    else .subnormal
  else if x.biasedExp.val = 255 then
    if x.mantissa.val = 0 then .infinity
    else .nan
  else .normal

/-- An F32 is finite if it is zero, subnormal, or normal. -/
def isFinite (x : F32) : Prop :=
  x.classify = .zero ∨ x.classify = .subnormal ∨ x.classify = .normal

instance : Decidable (isFinite x) := by
  unfold isFinite
  exact inferInstance

/-- An F32 is zero. -/
def isZero (x : F32) : Prop := x.classify = .zero

/-- An F32 is subnormal. -/
def isSubnormal (x : F32) : Prop := x.classify = .subnormal

/-- An F32 is normal. -/
def isNormal (x : F32) : Prop := x.classify = .normal

/-- Finite F32 values have biased exponent < 255. -/
@[simp] theorem finite_implies_exp_lt (x : F32) (hfin : x.isFinite) :
    x.biasedExp.val < 255 := by
  unfold isFinite classify at hfin
  have hbound := x.biasedExp.isLt
  rcases hfin with h | h | h <;> {
    split at h
    · split at h <;> simp at h <;> omega
    · split at h
      · split at h <;> simp at h
      · simp at h <;> omega
  }

@[simp] theorem exp_lt_implies_finite (x : F32) (h : x.biasedExp.val < 255) :
    x.isFinite := by
  unfold isFinite classify
  by_cases he : x.biasedExp.val = 0
  · by_cases hm : x.mantissa.val = 0
    · left; simp [he, hm]
    · right; left; simp [he, hm]
  · right; right; simp [he]; omega

end F32
