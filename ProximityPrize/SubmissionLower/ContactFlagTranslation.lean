import ProximityPrize.SubmissionLower.ContactFlagInterpolation
import ProximityPrize.SubmissionLower.ContactTranslation

namespace ProximityPrize.SubmissionLower.ContactFlagTranslation

open ContactFlagRankKernel ContactFlagInterpolation
open ContactTranslation
open ProximityPrize.Benchmark
open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K]

theorem columnMonomial_eq (D w L s : ℕ)
    (c : CoefficientIndex D w L s) (a : K) :
    MvPolynomial.monomial (columnExponent c) a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ c.2.2.2.val *
        MvPolynomial.X 1 ^ c.1.val * MvPolynomial.X 2 ^ c.2.1.val *
        MvPolynomial.X 3 ^ c.2.2.1.val := by
  rw [columnExponent, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem localMonomial_eq (f j z : ℕ) :
    localMonomial K f j z =
      MvPolynomial.X 0 ^ f * MvPolynomial.X 1 ^ j * MvPolynomial.X 2 ^ z := by
  rw [localMonomial, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial]

theorem translation_column (D w L s : ℕ) (x u₀ u₁ : K)
    (c : CoefficientIndex D w L s) (a : K) :
    ContactTranslation.homogenizedTranslation K x u₀ u₁
      (MvPolynomial.monomial (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
        (Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
          Polynomial.C (ContactInterpolation.seedAffine K u₀ u₁)) ^ c.1.val *
        Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
        Polynomial.C (MvPolynomial.X 2) ^ c.2.2.1.val := by
  rw [columnMonomial_eq K D w L s c a]
  simp [ContactTranslation.homogenizedTranslation,
    ContactTranslation.translationVariables,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem translation_column_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (c : CoefficientIndex D w L s) (a : K) (r : ℕ) :
    (homogenizedTranslation K x u₀ u₁
      (MvPolynomial.monomial (columnExponent c) a)).coeff r =
        a • blockEntry K D w L s x u₀ u₁ c r := by
  have hfactor :
      ContactTranslation.homogenizedTranslation K x u₀ u₁
        (MvPolynomial.monomial (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        ((Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
          (Polynomial.X * Polynomial.C (MvPolynomial.X 0) +
            Polynomial.C (ContactInterpolation.seedAffine K u₀ u₁)) ^ c.1.val *
          Polynomial.C (MvPolynomial.X 1 ^ c.2.1.val *
            MvPolynomial.X 2 ^ c.2.2.1.val)) := by
    rw [translation_column K D w L s x u₀ u₁ c a]
    simp only [map_mul, map_pow]
    ring
  rw [hfactor, Polynomial.coeff_C_mul, coeff_shifted_affine_product]
  unfold blockEntry
  rw [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  split_ifs with hfr
  · simp only [localMonomial_eq, MvPolynomial.smul_eq_C_mul,
      map_mul, map_pow, map_natCast, ContactInterpolation.seedAffine]
    ring
  · simp

theorem translation_reconstruct_coeff (D w L s : ℕ) (x u₀ u₁ : K)
    (θ : CoefficientIndex D w L s → K) (r : ℕ) :
    (ContactTranslation.homogenizedTranslation K x u₀ u₁
      (reconstruct K D w L s θ)).coeff r =
      ((extractBlock K D w L s x u₀ u₁ r θ) : Poly K) := by
  rw [reconstruct, map_sum, Polynomial.finsetSum_coeff]
  simp only [translation_column_coeff]
  change (∑ c : CoefficientIndex D w L s,
    θ c • blockEntry K D w L s x u₀ u₁ c r) =
      (((∑ c : CoefficientIndex D w L s,
        θ c • boundedBlockEntry K D w L s x u₀ u₁ c r) :
          coefficientBox K (min r L) L s) : Poly K)
  simp [boundedBlockEntry]

end

end ProximityPrize.SubmissionLower.ContactFlagTranslation
