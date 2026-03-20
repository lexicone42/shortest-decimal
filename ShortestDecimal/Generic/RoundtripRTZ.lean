/-
  Generic/RoundtripRTZ.lean

  THE GENERIC RTZ ROUNDTRIP THEOREM: any DecimalConversionAlgorithmRTZ
  satisfying the interface produces correct roundtrip results under
  round-toward-zero.
-/
import ShortestDecimal.Generic.AlgorithmRTZ

namespace ShortestDecimal

/-- Convert a Decimal to F64 via round-toward-zero.
    For zero digits, construct the F64 directly (preserving sign). -/
def Decimal.toF64_rtz (d : Decimal) : F64 :=
  if d.digits = 0 then ⟨d.sign, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  else F64.roundTowardZero d.toRat

/-! ## Helper -/

private theorem digits_zero_toRat_zero (d : Decimal) (h : d.digits = 0) :
    d.toRat = 0 := by
  unfold Decimal.toRat; simp [h]

/-! ## The Generic RTZ Roundtrip Theorem -/

/-- THE GENERIC RTZ ROUNDTRIP THEOREM.

    For ANY decimal conversion algorithm satisfying the RTZ interface,
    and for ANY finite IEEE 754 double x:
      parse(format(algorithm(x))).toF64_rtz roundtrips to x. -/
theorem generic_full_roundtrip_rtz (alg : DecimalConversionAlgorithmRTZ)
    (x : F64) (hfin : x.isFinite) :
    (Decimal.parse (Decimal.format (alg.convert x hfin))).map Decimal.toF64_rtz = some x := by
  by_cases h0 : x.toRat = 0
  · -- Zero case
    have hd0 := alg.zero_digits x hfin h0
    have hsign := alg.zero_sign x hfin h0
    rw [Decimal.format_parse_roundtrip _ (alg.well_formed x hfin)]
    simp [Option.map, Decimal.toF64_rtz, hd0]
    have hsig_zero : x.effectiveSignificand = 0 := by
      by_contra hsig
      have hsig_ne : (x.effectiveSignificand : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsig
      have hsign_ne : (if x.sign then (-1 : ℚ) else 1) ≠ 0 := by split <;> norm_num
      unfold F64.toRat at h0; rw [if_neg (not_not.mpr hfin)] at h0; simp only [] at h0
      split at h0
      · exact absurd h0 (mul_ne_zero (mul_ne_zero hsign_ne hsig_ne) (by positivity))
      · rw [div_eq_zero_iff] at h0
        exact h0.elim (absurd · (mul_ne_zero hsign_ne hsig_ne)) (absurd · (by positivity))
    have hbexp : x.biasedExp.val = 0 := by
      by_contra h; unfold F64.effectiveSignificand at hsig_zero; simp [h, F64.mantBits] at hsig_zero
    have hmant : x.mantissa.val = 0 := by
      unfold F64.effectiveSignificand at hsig_zero; simp [hbexp] at hsig_zero; omega
    rcases x with ⟨s, ⟨e, he⟩, ⟨m, hm⟩⟩
    simp only [] at hbexp hmant
    have he0 : e = 0 := by omega
    have hm0 : m = 0 := by omega
    subst he0; subst hm0
    simp only [F64.mk.injEq]
    exact ⟨hsign, rfl, rfl⟩
  · -- Non-zero case
    have hwf := alg.well_formed x hfin
    have h_in := alg.in_interval x hfin h0
    rw [Decimal.format_parse_roundtrip _ hwf]
    simp [Option.map]
    have hd_ne : (alg.convert x hfin).digits ≠ 0 := by
      intro hd0
      have := digits_zero_toRat_zero _ hd0
      rw [this] at h_in
      have ⟨hlo, _⟩ := ShortestDecimal.rtz_abs_interval_pos x hfin h0
      unfold ShortestDecimal.AcceptanceInterval.contains at h_in
      cases hs : x.sign <;> simp [hs] at hlo h_in
      · obtain ⟨h, _⟩ := h_in; split at h <;> linarith
      · obtain ⟨_, h⟩ := h_in; split at h <;> linarith
    simp [Decimal.toF64_rtz, hd_ne]
    exact ShortestDecimal.rtz_interval_correct x hfin h0 _ h_in

/-- Corollary: the algorithm's Decimal, converted to F64 via RTZ, gives x. -/
theorem generic_decimal_roundtrip_rtz (alg : DecimalConversionAlgorithmRTZ)
    (x : F64) (hfin : x.isFinite) :
    Decimal.toF64_rtz (alg.convert x hfin) = x := by
  have h := generic_full_roundtrip_rtz alg x hfin
  rw [Decimal.format_parse_roundtrip _ (alg.well_formed x hfin)] at h
  simp [Option.map] at h; exact h

end ShortestDecimal
