import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount

/-!
# Zero counting from an arbitrary affine separating parameter

Research module, deliberately kept off the green submission chain.

The production actual-curve theorem chooses one of the three literal
coordinates as its rational-function base.  The adaptive shear instead
needs the affine element `S = R + Z`.  This file proves that the existing
normalization/place machinery accepts such a parameter without changing
the affine model or transporting its prime ideal.

The only data required of the new parameter are its literal element in the
affine coordinate ring, a compatible rational-function embedding in the
fraction field, and finite separability.  No degree or point-count bound is
assumed by the structure.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveArbitraryProjectionZeroCountResearch

open scoped Classical TensorProduct
open CoordinateBoxZeroCount

noncomputable section

variable (K A L : Type*) [Field K] [CommRing A] [IsDomain A] [Field L]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra K L] [IsScalarTower K A L]

/-- Canonical rational-function evaluation at any transcendental element,
not only at one of the three named coordinates. -/
def rationalEmbeddingAt (x : L) (hx : Transcendental K x) :
    RatFunc K →ₐ[K] L :=
  RatFunc.liftAlgHom (Polynomial.aeval x)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (Polynomial.aeval x).toRingHom
      (transcendental_iff_injective.mp hx))

theorem rationalEmbeddingAt_polynomial (x : L) (hx : Transcendental K x)
    (f : Polynomial K) :
    rationalEmbeddingAt K L x hx
        (algebraMap (Polynomial K) (RatFunc K) f) =
      Polynomial.aeval x f :=
  RatFunc.liftRingHom_algebraMap _ _ f

theorem rationalEmbeddingAt_variable (x : L) (hx : Transcendental K x) :
    rationalEmbeddingAt K L x hx
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
  rw [rationalEmbeddingAt_polynomial, Polynomial.aeval_X]

/-- A finite separable rational projection whose parameter is represented
by a literal element of the chosen affine model. -/
structure AffineSeparableProjection where
  modelValue : A
  embedding : RatFunc K →ₐ[K] L
  value_eq :
    embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
      algebraMap A L modelValue
  finite : letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) L
  separable : letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
    Algebra.IsSeparable (RatFunc K) L

namespace AffineSeparableProjection

/-- Build the compatible affine projection once transcendence, finiteness,
and separability of the induced extension have been established. -/
def ofTranscendental (a : A)
    (ha : Transcendental K (algebraMap A L a))
    (hfinite :
      letI : Algebra (RatFunc K) L :=
        (rationalEmbeddingAt K L (algebraMap A L a) ha).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hseparable :
      letI : Algebra (RatFunc K) L :=
        (rationalEmbeddingAt K L (algebraMap A L a) ha).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) L) :
    AffineSeparableProjection K A L where
  modelValue := a
  embedding := rationalEmbeddingAt K L (algebraMap A L a) ha
  value_eq := rationalEmbeddingAt_variable K L _ ha
  finite := hfinite
  separable := hseparable

abbrev ratFuncAlgebra (q : AffineSeparableProjection K A L) :
    Algebra (RatFunc K) L := q.embedding.toRingHom.toAlgebra

abbrev modelPolynomialAlgebra (q : AffineSeparableProjection K A L) :
    Algebra (Polynomial K) A :=
  (Polynomial.aeval q.modelValue).toRingHom.toAlgebra

abbrev fieldPolynomialAlgebra (q : AffineSeparableProjection K A L) :
    Algebra (Polynomial K) L :=
  ((q.embedding.comp
    (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))).toRingHom).toAlgebra

theorem embedding_polynomial (q : AffineSeparableProjection K A L)
    (f : Polynomial K) :
    q.embedding (algebraMap (Polynomial K) (RatFunc K) f) =
      Polynomial.aeval (algebraMap A L q.modelValue) f := by
  have hhom :
      q.embedding.comp
          (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)) =
        Polynomial.aeval (algebraMap A L q.modelValue) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      Polynomial.aeval_X]
    change q.embedding
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        algebraMap A L q.modelValue
    exact q.value_eq
  exact DFunLike.congr_fun hhom f

theorem tower_K_polynomial_model (q : AffineSeparableProjection K A L) :
    letI : Algebra (Polynomial K) A := q.modelPolynomialAlgebra
    IsScalarTower K (Polynomial K) A := by
  letI : Algebra (Polynomial K) A := q.modelPolynomialAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c ↦
    ((Polynomial.aeval q.modelValue).commutes c).symm

theorem tower_K_polynomial_field (q : AffineSeparableProjection K A L) :
    letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
    IsScalarTower K (Polynomial K) L := by
  letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap K L c = q.embedding
      (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c))
    rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
    exact (q.embedding.commutes c).symm

theorem tower_K_ratFunc_field (q : AffineSeparableProjection K A L) :
    letI : Algebra (RatFunc K) L := q.ratFuncAlgebra
    IsScalarTower K (RatFunc K) L := by
  letI : Algebra (RatFunc K) L := q.ratFuncAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c ↦ (q.embedding.commutes c).symm

theorem tower_polynomial_ratFunc_field
    (q : AffineSeparableProjection K A L) :
    letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
    letI : Algebra (RatFunc K) L := q.ratFuncAlgebra
    IsScalarTower (Polynomial K) (RatFunc K) L := by
  letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
  letI : Algebra (RatFunc K) L := q.ratFuncAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

theorem model_polynomial_fraction (q : AffineSeparableProjection K A L)
    (f : Polynomial K) :
    algebraMap A L (Polynomial.aeval q.modelValue f) =
      q.embedding (algebraMap (Polynomial K) (RatFunc K) f) := by
  rw [q.embedding_polynomial]
  have hhom :
      (IsScalarTower.toAlgHom K A L).comp (Polynomial.aeval q.modelValue) =
        Polynomial.aeval (algebraMap A L q.modelValue) := by
    apply Polynomial.algHom_ext
    simp
  exact DFunLike.congr_fun hhom f

theorem tower_polynomial_model_field
    (q : AffineSeparableProjection K A L) :
    letI : Algebra (Polynomial K) A := q.modelPolynomialAlgebra
    letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
    IsScalarTower (Polynomial K) A L := by
  letI : Algebra (Polynomial K) A := q.modelPolynomialAlgebra
  letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
  exact IsScalarTower.of_algebraMap_eq fun f ↦
    (model_polynomial_fraction K A L q f).symm

variable [IsAlgClosed K]
variable { σ : Type* } [Fintype σ]

/-- The existing affine-model point count with an arbitrary compatible
finite separable parameter installed as the common separator. -/
theorem finite_model_zero_points_le_box
    (q : AffineSeparableProjection K A L)
    (x : σ → A) (c : σ → Coordinate K L)
    (hc : ∀ i, coordinateValue K L (c i) = algebraMap A L (x i))
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K A) x F ≠ 0)
    (S : Finset (A →ₐ[K] K))
    (hS : ∀ φ ∈ S, φ (MvPolynomial.eval₂Hom (algebraMap K A) x F) = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * (coordinateDegree K L (c i) : ℤ) := by
  letI : Algebra (Polynomial K) A := q.modelPolynomialAlgebra
  letI : Algebra (Polynomial K) L := q.fieldPolynomialAlgebra
  letI : Algebra (RatFunc K) L := q.ratFuncAlgebra
  letI : IsScalarTower K (Polynomial K) A := q.tower_K_polynomial_model
  letI : IsScalarTower K (Polynomial K) L := q.tower_K_polynomial_field
  letI : IsScalarTower K (RatFunc K) L := q.tower_K_ratFunc_field
  letI : IsScalarTower (Polynomial K) (RatFunc K) L :=
    q.tower_polynomial_ratFunc_field
  letI : IsScalarTower (Polynomial K) A L := q.tower_polynomial_model_field
  letI : FiniteDimensional (RatFunc K) L := q.finite
  letI : Algebra.IsSeparable (RatFunc K) L := q.separable
  exact CoordinateBoxZeroCount.finite_model_zero_points_le_box
    K L A x c hc cap F hcap hF S hS

end AffineSeparableProjection

end

end ProximityPrize.SubmissionLower.ActualCurveArbitraryProjectionZeroCountResearch

#print axioms ProximityPrize.SubmissionLower.ActualCurveArbitraryProjectionZeroCountResearch.AffineSeparableProjection.finite_model_zero_points_le_box
