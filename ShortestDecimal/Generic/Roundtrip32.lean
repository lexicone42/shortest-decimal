/-
  Generic/Roundtrip32.lean

  The generic roundtrip theorem for F32 (IEEE 754 binary32).
  Mirrors Generic/Roundtrip.lean with F32 types.
-/
import ShortestDecimal.Generic.Algorithm32
import ShortestDecimal.Roundtrip.FormatParse

namespace ShortestDecimal

private theorem digits_zero_toRat_zero₃₂ (d : Decimal) (h : d.digits = 0) :
    d.toRat = 0 := by
  unfold Decimal.toRat; simp [h]

/-- THE GENERIC ROUNDTRIP THEOREM FOR F32.

    For ANY decimal conversion algorithm satisfying the F32 interface,
    and for ANY finite IEEE 754 single-precision float x:
      parse(format(algorithm(x))) roundtrips to x. -/
theorem generic_full_roundtrip32 (alg : DecimalConversionAlgorithm32)
    (x : F32) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (alg.convert x hfin))).map Decimal.toF32 = some x := by
  by_cases h0 : x.toRat = 0
  · have hd0 := alg.zero_digits x hfin h0
    have hsign := alg.zero_sign x hfin h0
    rw [Decimal.format_parse_roundtrip _ (alg.well_formed x hfin)]
    simp [Option.map, Decimal.toF32, hd0]
    have hsig_zero : x.effectiveSignificand = 0 := by
      by_contra hsig
      have hsig_ne : (x.effectiveSignificand : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsig
      have hsign_ne : (if x.sign then (-1 : ℚ) else 1) ≠ 0 := by split <;> norm_num
      unfold F32.toRat at h0; rw [if_neg (not_not.mpr hfin)] at h0; simp only [] at h0
      split at h0
      · exact absurd h0 (mul_ne_zero (mul_ne_zero hsign_ne hsig_ne) (by positivity))
      · rw [div_eq_zero_iff] at h0
        exact h0.elim (absurd · (mul_ne_zero hsign_ne hsig_ne)) (absurd · (by positivity))
    have hbexp : x.biasedExp.val = 0 := by
      by_contra h; unfold F32.effectiveSignificand at hsig_zero
      simp [h, F32.mantBits] at hsig_zero
    have hmant : x.mantissa.val = 0 := by
      unfold F32.effectiveSignificand at hsig_zero; simp [hbexp] at hsig_zero; omega
    rcases x with ⟨s, ⟨e, _⟩, ⟨m, _⟩⟩
    simp only [] at hbexp hmant hsign
    have he0 : e = 0 := by omega
    have hm0 : m = 0 := by omega
    subst he0; subst hm0
    simp only [F32.mk.injEq]
    exact ⟨hsign, rfl, rfl⟩
  · have hwf := alg.well_formed x hfin
    have h_in := alg.in_interval x hfin h0
    rw [Decimal.format_parse_roundtrip _ hwf]
    simp [Option.map]
    have hd_ne : (alg.convert x hfin).digits ≠ 0 := by
      intro hd0
      have := digits_zero_toRat_zero₃₂ _ hd0
      rw [this] at h_in
      have ⟨hlo, _⟩ := schubfach_abs_interval_pos32 x hfin h0
      unfold ShortestDecimal.AcceptanceInterval.contains at h_in
      cases hs : x.sign <;> simp [hs] at hlo h_in
      · obtain ⟨h, _⟩ := h_in; split at h <;> linarith
      · obtain ⟨_, h⟩ := h_in; split at h <;> linarith
    simp [Decimal.toF32, hd_ne]
    exact schubfach_interval_correct32 x hfin h0 _ h_in

/-- Corollary: the algorithm's Decimal, converted to F32, gives x. -/
theorem generic_decimal_roundtrip32 (alg : DecimalConversionAlgorithm32)
    (x : F32) (hfin : x.isFinite) :
    (alg.convert x hfin).toF32 = x := by
  have h := generic_full_roundtrip32 alg x hfin
  rw [Decimal.format_parse_roundtrip _ (alg.well_formed x hfin)] at h
  simp [Option.map] at h; exact h

end ShortestDecimal
