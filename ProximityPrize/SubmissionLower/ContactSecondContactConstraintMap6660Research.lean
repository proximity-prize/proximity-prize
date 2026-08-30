import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactUVSpan6660Research

 







namespace ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research

open ContactSecondContactSFreeInterpolation6660Research
open ContactSecondContactUVSpan6660Research
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.checkUnivs false

noncomputable section

section GenericExpansion

variable {A : Type*} [CommRing A]

 

theorem affine_double_expansion (T U zeta xc u0c u1c : A) (a y : ℕ) :
    (T + xc) ^ a * (U + (u0c + zeta * u1c)) ^ y =
      ∑ k ∈ Finset.range (a + 1),
        ∑ v ∈ Finset.range (y + 1),
          ∑ i ∈ Finset.range (y - v + 1),
            ((a.choose k : ℕ) : A) * ((y.choose v : ℕ) : A) *
              (((y - v).choose i : ℕ) : A) *
              T ^ k * U ^ v * zeta ^ (y - v - i) *
              xc ^ (a - k) * u0c ^ i * u1c ^ (y - v - i) := by
  rw [add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_pow]
  ring

end GenericExpansion

variable (K : Type*) [Field K]

abbrev Outer := ContactSecondContactUVSpan6660Research.Outer K

theorem lowJet_scalar_mul (m : ℕ) (a : K) (P : Outer K) :
    lowJet K m (Polynomial.C (MvPolynomial.C a) * P) =
      a • lowJet K m P := by
  funext j
  change (Polynomial.C (MvPolynomial.C a) * P).coeff j.val =
    (a : K) • P.coeff j.val
  rw [Polynomial.coeff_C_mul]
  simp only [MvPolynomial.smul_eq_C_mul]

theorem columnMonomial_eq {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) (a : K) :
    MvPolynomial.monomial (columnExponent c) a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ c.2.2.2.val *
        MvPolynomial.X 1 ^ c.1.val * MvPolynomial.X 2 ^ c.2.1.val *
        MvPolynomial.X 3 ^ c.2.2.1.val := by
  rw [columnExponent, MvPolynomial.monomial_add_single,
    MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem translatedY_eq (x u0 u1 : K) :
    translationVariables K x u0 u1 1 =
      Polynomial.C (seedAffine K u0 u1) + contactU K := by
  simp [translationVariables, contactU, contactV, contactTail]
  ring

theorem translation_column {D w C rCap : ℕ}
    (x u0 u1 : K) (c : CoefficientIndex D w C rCap) (a : K) :
    secondContactTranslation K x u0 u1
        (MvPolynomial.monomial (columnExponent c) a) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
        (contactU K + Polynomial.C (seedAffine K u0 u1)) ^ c.1.val *
        Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
        Polynomial.C (MvPolynomial.X 3) ^ c.2.2.1.val := by
  rw [columnMonomial_eq K c a]
  simp [secondContactTranslation, translationVariables, contactU, contactV,
    contactTail, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  ring <;> simp

 

def expansionScalar (a x u0 u1 : K) (ax y k v i : ℕ) : K :=
  a * (ax.choose k : K) * (y.choose v : K) * ((y - v).choose i : K) *
    x ^ (ax - k) * u0 ^ i * u1 ^ (y - v - i)

theorem translated_column_expansion {D w C rCap : ℕ}
    (x u0 u1 : K) (c : CoefficientIndex D w C rCap) (a : K) :
    secondContactTranslation K x u0 u1
        (MvPolynomial.monomial (columnExponent c) a) =
      ∑ k ∈ Finset.range (c.2.2.2.val + 1),
        ∑ v ∈ Finset.range (c.1.val + 1),
          ∑ i ∈ Finset.range (c.1.val - v + 1),
            Polynomial.C (MvPolynomial.C
              (expansionScalar K a x u0 u1 c.2.2.2.val c.1.val k v i)) *
              centeredGenerator K k v c.2.1.val
                (c.2.2.1.val + (c.1.val - v - i)) := by
  rw [translation_column K x u0 u1 c a]
  have hseed : Polynomial.C (seedAffine K u0 u1) =
      Polynomial.C (MvPolynomial.C u0) +
        Polynomial.C (MvPolynomial.X 3) * Polynomial.C (MvPolynomial.C u1) := by
    simp [seedAffine]
  rw [hseed]
  calc
    Polynomial.C (MvPolynomial.C a) *
          (Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
          (contactU K + (Polynomial.C (MvPolynomial.C u0) +
            Polynomial.C (MvPolynomial.X 3) * Polynomial.C (MvPolynomial.C u1))) ^
              c.1.val *
          Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
          Polynomial.C (MvPolynomial.X 3) ^ c.2.2.1.val =
        Polynomial.C (MvPolynomial.C a) *
          ((Polynomial.X + Polynomial.C (MvPolynomial.C x)) ^ c.2.2.2.val *
            (contactU K + (Polynomial.C (MvPolynomial.C u0) +
              Polynomial.C (MvPolynomial.X 3) * Polynomial.C (MvPolynomial.C u1))) ^
                c.1.val) *
          Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
          Polynomial.C (MvPolynomial.X 3) ^ c.2.2.1.val := by ring
    _ = Polynomial.C (MvPolynomial.C a) *
          (∑ k ∈ Finset.range (c.2.2.2.val + 1),
            ∑ v ∈ Finset.range (c.1.val + 1),
              ∑ i ∈ Finset.range (c.1.val - v + 1),
                (((c.2.2.2.val.choose k : ℕ) : Outer K) *
                  ((c.1.val.choose v : ℕ) : Outer K) *
                  (((c.1.val - v).choose i : ℕ) : Outer K) *
                  Polynomial.X ^ k * contactU K ^ v *
                  Polynomial.C (MvPolynomial.X 3) ^ (c.1.val - v - i) *
                  Polynomial.C (MvPolynomial.C x) ^ (c.2.2.2.val - k) *
                  Polynomial.C (MvPolynomial.C u0) ^ i *
                  Polynomial.C (MvPolynomial.C u1) ^ (c.1.val - v - i))) *
          Polynomial.C (MvPolynomial.X 1) ^ c.2.1.val *
          Polynomial.C (MvPolynomial.X 3) ^ c.2.2.1.val := by
      rw [affine_double_expansion]
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [centeredGenerator, expansionScalar, map_mul, map_pow, map_natCast]
      rw [pow_add]
      ring

 


theorem lowJet_translation_column_mem_uvSpan {D w C rCap : ℕ}
    (m : ℕ) (x u0 u1 : K) (c : CoefficientIndex D w C rCap) (a : K) :
    lowJet K m (secondContactTranslation K x u0 u1
      (MvPolynomial.monomial (columnExponent c) a)) ∈ uvSpan K m C rCap := by
  classical
  rw [translated_column_expansion K x u0 u1 c a]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.sum_mem
  intro i hi
  have hvle : v ≤ c.1.val := by
    have := Finset.mem_range.mp hv
    omega
  have hile : i ≤ c.1.val - v := by
    have := Finset.mem_range.mp hi
    omega
  have htotal :
      v + c.2.1.val + (c.2.2.1.val + (c.1.val - v - i)) ≤ C := by
    have hy := c.1.isLt
    have hr := c.2.1.isLt
    have hz := c.2.2.1.isLt
    omega
  have hrCap : c.2.1.val ≤ rCap := by
    have := c.2.1.isLt
    omega
  rw [lowJet_scalar_mul]
  exact Submodule.smul_mem _ _
    (lowJet_centeredGenerator_mem_uvSpan K m C rCap k v c.2.1.val
      (c.2.2.1.val + (c.1.val - v - i)) hrCap htotal)

end

end ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research.affine_double_expansion
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research.translation_column
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research.lowJet_translation_column_mem_uvSpan
