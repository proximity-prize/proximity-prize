import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AffineModelPointLift

/-!
# Actual affine-model places in the constructed function-field normalization

Model label: gpt-5.

This specializes the actual model-point construction to the integral
closure of K[T] in the given finite separable function-field extension.
All normalization properties and both injectivity conditions are derived.
The model A is not assumed integral over K[T].
-/

namespace ProximityPrize.SubmissionLower.ActualAffineModelPlaces

open IsDedekindDomain

noncomputable section

variable (K A L : Type*) [Field K] [IsAlgClosed K]
  [CommRing A] [IsDomain A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsFractionRing A L]
  [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower K (Polynomial K) A] [IsScalarTower K (Polynomial K) L]
  [IsScalarTower K A L] [IsScalarTower (Polynomial K) A L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

abbrev Normalization := FunctionField.ringOfIntegers K L

/-- The codomain is the actual constructed normalization, not an input. -/
def actualPointPlace (φ : A →ₐ[K] K) : HeightOneSpectrum (Normalization K L) :=
  AffineModelPointLift.modelPointPlace
    (FunctionField.ringOfIntegers.algebraMap_injective K L)
    (IsFractionRing.injective A L) φ

theorem actualPointPlace_injective :
    Function.Injective (actualPointPlace K A L) :=
  AffineModelPointLift.modelPointPlace_injective
    (FunctionField.ringOfIntegers.algebraMap_injective K L)
    (IsFractionRing.injective A L)

theorem actual_model_value_le_one (φ : A →ₐ[K] K) (a : A) :
    (actualPointPlace K A L φ).valuation L (algebraMap A L a) ≤ 1 :=
  AffineModelPointLift.model_value_le_one
    (FunctionField.ringOfIntegers.algebraMap_injective K L)
    (IsFractionRing.injective A L) φ a

theorem actual_model_value_lt_one_iff (φ : A →ₐ[K] K) (a : A) :
    (actualPointPlace K A L φ).valuation L (algebraMap A L a) < 1 ↔ φ a = 0 :=
  AffineModelPointLift.model_value_lt_one_iff
    (FunctionField.ringOfIntegers.algebraMap_injective K L)
    (IsFractionRing.injective A L) φ a

theorem actual_model_zero_order_ge_one
    (φ : A →ₐ[K] K) (a : A) (ha : a ≠ 0) (hzero : φ a = 0) :
    1 ≤ -((actualPointPlace K A L φ).valuation L (algebraMap A L a)).log :=
  AffineModelPointLift.model_zero_order_ge_one
    (FunctionField.ringOfIntegers.algebraMap_injective K L)
    (IsFractionRing.injective A L) φ a ha hzero

end

end ProximityPrize.SubmissionLower.ActualAffineModelPlaces

#print axioms ProximityPrize.SubmissionLower.ActualAffineModelPlaces.actualPointPlace
#print axioms ProximityPrize.SubmissionLower.ActualAffineModelPlaces.actualPointPlace_injective
#print axioms ProximityPrize.SubmissionLower.ActualAffineModelPlaces.actual_model_value_le_one
#print axioms ProximityPrize.SubmissionLower.ActualAffineModelPlaces.actual_model_value_lt_one_iff
#print axioms ProximityPrize.SubmissionLower.ActualAffineModelPlaces.actual_model_zero_order_ge_one
