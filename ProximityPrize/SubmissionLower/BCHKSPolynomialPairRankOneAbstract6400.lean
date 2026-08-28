import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminantSpan6400

/-!
# Abstract non-primitivity in a rank-one polynomial-pair family

This module isolates the small algebraic argument from the production Cramer
construction so the latter can be compiled in a separate memory envelope.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

/-- A finite linearly independent family of at least two polynomial pairs
whose pairwise determinants vanish contains a non-coprime member. -/
theorem exists_nonCoprime_member_of_linearIndependent_pairDet_eq_zero
    {F J : Type} [Field F] [Fintype J]
    {c h : Nat}
    (family : J → PolynomialPairSpace F c h)
    (hLI : LinearIndependent F family)
    (hcard : 2 ≤ Fintype.card J)
    (hdet : ∀ i j, polynomialPairDet (family i) (family j) = 0) :
    ∃ j, ¬ IsCoprime (family j).1.1 (family j).2.1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hJpos : 0 < Fintype.card J := by omega
  let j₀ : J := Classical.choice (Fintype.card_pos_iff.mp hJpos)
  have hscalar : ∀ j, ∃ a : F, family j = a • family j₀ := by
    intro j
    by_cases hA₀ : (family j₀).1.1 ≠ 0
    · have hcross :
          (family j₀).1.1 * (family j).2.1 =
            (family j₀).2.1 * (family j).1.1 := by
        exact sub_eq_zero.mp (by
          simpa only [polynomialPairDet] using hdet j₀ j)
      obtain ⟨s, hsA, hsB⟩ :=
        exists_polynomial_multiplier_of_coprime_cross
          (family j₀).1.1 (family j₀).2.1
          (family j).1.1 (family j).2.1 hA₀ (hnone j₀) hcross
      obtain ⟨r, t, hbezout⟩ := hnone j
      have hsone : s ∣ 1 := by
        refine ⟨r * (family j₀).1.1 + t * (family j₀).2.1, ?_⟩
        calc
          1 = r * (family j).1.1 + t * (family j).2.1 := hbezout.symm
          _ = s * (r * (family j₀).1.1 +
              t * (family j₀).2.1) := by rw [hsA, hsB]; ring
      have hsunit : IsUnit s := isUnit_iff_dvd_one.mpr hsone
      obtain ⟨a, _haunit, hCa⟩ := Polynomial.isUnit_iff.mp hsunit
      refine ⟨a, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change (family j).1.1 = a • (family j₀).1.1
        rw [hsA, ← hCa]
        simp only [smul_eq_C_mul]
      · apply Subtype.ext
        change (family j).2.1 = a • (family j₀).2.1
        rw [hsB, ← hCa]
        simp only [smul_eq_C_mul]
    · have hA₀zero : (family j₀).1.1 = 0 := not_ne_iff.mp hA₀
      have hB₀unit : IsUnit (family j₀).2.1 := by
        rw [← isCoprime_zero_left, ← hA₀zero]
        exact hnone j₀
      have hB₀ne : (family j₀).2.1 ≠ 0 := hB₀unit.ne_zero
      have hAjzero : (family j).1.1 = 0 := by
        have hproduct : (family j₀).2.1 * (family j).1.1 = 0 := by
          have hz := hdet j₀ j
          simpa only [polynomialPairDet, hA₀zero, zero_mul, zero_sub,
            neg_eq_zero] using hz
        exact (mul_eq_zero.mp hproduct).resolve_left hB₀ne
      have hBjunit : IsUnit (family j).2.1 := by
        rw [← isCoprime_zero_left, ← hAjzero]
        exact hnone j
      obtain ⟨b₀, hb₀unit, hb₀⟩ := Polynomial.isUnit_iff.mp hB₀unit
      obtain ⟨b, _hbunit, hb⟩ := Polynomial.isUnit_iff.mp hBjunit
      have hb₀ne : b₀ ≠ 0 := hb₀unit.ne_zero
      let a : F := b * b₀⁻¹
      refine ⟨a, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change (family j).1.1 = a • (family j₀).1.1
        simp only [hAjzero, hA₀zero, smul_zero]
      · apply Subtype.ext
        change (family j).2.1 = a • (family j₀).2.1
        rw [← hb, ← hb₀, smul_eq_C_mul, ← Polynomial.C_mul]
        congr 1
        dsimp only [a]
        field_simp
  have hspan :
      Submodule.span F (Set.range family) ≤ F ∙ family j₀ := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hscalar j
    exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩
  have hfinrank := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hLI,
    finrank_span_singleton (hLI.ne_zero j₀)] at hfinrank
  omega

end ProximityPrize.SubmissionLower
