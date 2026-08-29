import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AffineOverringPointValuation
import ProximityPrize.SubmissionLower.IntegralPointLifting


/-!
# Constructed point-to-place maps for actual affine models

Model label: gpt-5.

The affine model A need not be integral over the coordinate ring K[T].
We construct B = integralClosure A L, lift each actual K-valued point to B,
and restrict it to the actual Dedekind normalization S of K[T] in L.
The overring fraction argument gives an injective point-to-place map,
unit-ball bounds on all model functions, and positive orders at zeros.

No point lift, place assignment, or zero-count inequality is assumed.
-/

namespace ProximityPrize.SubmissionLower.AffineModelPointLift

open IsDedekindDomain AffinePointValuation AffineOverringPointValuation

noncomputable section

abbrev ModelClosure (A L : Type*) [CommRing A] [Field L] [Algebra A L] :=
  integralClosure A L

section Construction

variable {K S A L : Type*} [Field K] [IsAlgClosed K]
  [CommRing S] [IsDedekindDomain S] [CommRing A] [Field L]
  [Algebra K S] [Algebra K A] [Algebra K L]
  [Algebra (Polynomial K) S] [Algebra (Polynomial K) A] [Algebra (Polynomial K) L]
  [Algebra S L] [Algebra A L]
  [IsScalarTower K (Polynomial K) S] [IsScalarTower K (Polynomial K) A]
  [IsScalarTower K (Polynomial K) L] [IsScalarTower K S L] [IsScalarTower K A L]
  [IsScalarTower (Polynomial K) S L] [IsScalarTower (Polynomial K) A L]
  [IsFractionRing S L] [Algebra.IsIntegral (Polynomial K) S]

/-- The actual normalization S maps into the integral closure of A:
its monic K[T]-relations remain monic relations over A. -/
def inclusionToModelClosure : S →ₐ[K] ModelClosure A L where
  toFun s := ⟨algebraMap S L s, by
    have hs : IsIntegral (Polynomial K) (algebraMap S L s) :=
      (Algebra.IsIntegral.isIntegral (R := Polynomial K) s).map
        (IsScalarTower.toAlgHom (Polynomial K) S L)
    exact hs.tower_top⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  commutes' c := by
    apply Subtype.ext
    change algebraMap S L (algebraMap K S c) = algebraMap K L c
    exact (IsScalarTower.algebraMap_apply K S L c).symm

theorem modelClosure_base_injective
    (hinj : Function.Injective (algebraMap A L)) :
    Function.Injective (algebraMap A (ModelClosure A L)) := by
  intro a b h
  apply hinj
  exact congrArg (fun x : ModelClosure A L => (x : L)) h

theorem modelClosure_embedding_injective :
    Function.Injective (algebraMap (ModelClosure A L) L) :=
  Subtype.val_injective

/-- The actual integral-closure point is constructed by lying over and
algebraic closedness, using the previously verified lifting theorem. -/
def modelClosurePoint (hinj : Function.Injective (algebraMap A L))
    (φ : A →ₐ[K] K) : ModelClosure A L →ₐ[K] K :=
  IntegralPointLifting.chosenPointLift (modelClosure_base_injective hinj) φ

theorem modelClosurePoint_restrict
    (hinj : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K) (a : A) :
    modelClosurePoint hinj φ (algebraMap A (ModelClosure A L) a) = φ a :=
  AlgHom.congr_fun
    (IntegralPointLifting.chosenPointLift_spec (modelClosure_base_injective hinj) φ) a

/-- Restriction of the constructed point to S gives an actual nonzero
height-one prime, with nonzeroness witnessed by T-φ(T). -/
def modelPointPlace
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K) :
    HeightOneSpectrum S :=
  pointPlace hS ((modelClosurePoint hA φ).comp
    (inclusionToModelClosure (K := K) (S := S) (A := A) (L := L)))

theorem modelPointPlace_kernel
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K) :
    RingHom.ker ((modelClosurePoint hA φ).toRingHom.comp
      (inclusionToModelClosure (K := K) (S := S) (A := A) (L := L)).toRingHom) =
      (modelPointPlace hS hA φ).asIdeal := rfl

theorem model_value_le_one
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K) (a : A) :
    (modelPointPlace hS hA φ).valuation L (algebraMap A L a) ≤ 1 := by
  letI : Algebra S (ModelClosure A L) :=
    (inclusionToModelClosure (K := K) (S := S) (A := A) (L := L)).toRingHom.toAlgebra
  letI : IsScalarTower S (ModelClosure A L) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := overring_value_le_one (L := L) modelClosure_embedding_injective
    (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
    (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
  simpa only [← IsScalarTower.algebraMap_apply A (ModelClosure A L) L] using h

theorem model_value_lt_one_iff
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K) (a : A) :
    (modelPointPlace hS hA φ).valuation L (algebraMap A L a) < 1 ↔ φ a = 0 := by
  letI : Algebra S (ModelClosure A L) :=
    (inclusionToModelClosure (K := K) (S := S) (A := A) (L := L)).toRingHom.toAlgebra
  letI : IsScalarTower S (ModelClosure A L) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h := overring_value_lt_one_iff (L := L) modelClosure_embedding_injective
    (modelPointPlace hS hA φ) (modelClosurePoint hA φ).toRingHom
    (modelPointPlace_kernel hS hA φ) (algebraMap A (ModelClosure A L) a)
  simpa only [← IsScalarTower.algebraMap_apply A (ModelClosure A L) L,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, modelClosurePoint_restrict] using h

/-- Different original affine points cannot collapse to the same
normalization prime, even though the lifted points were chosen. -/
theorem modelPointPlace_injective
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) :
    Function.Injective (modelPointPlace hS hA : (A →ₐ[K] K) → HeightOneSpectrum S) := by
  intro φ ψ h
  apply AffinePointValuation.pointKernel_injective
  apply Ideal.ext
  intro a
  change φ a = 0 ↔ ψ a = 0
  rw [← model_value_lt_one_iff hS hA φ a, ← model_value_lt_one_iff hS hA ψ a, h]

theorem model_zero_order_ge_one
    (hS : Function.Injective (algebraMap (Polynomial K) S))
    (hA : Function.Injective (algebraMap A L)) (φ : A →ₐ[K] K)
    (a : A) (ha : a ≠ 0) (hzero : φ a = 0) :
    1 ≤ -((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log := by
  have hv0 : (modelPointPlace hS hA φ).valuation L (algebraMap A L a) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by simpa only [map_zero] using hA.ne ha)
  have hvlt := (model_value_lt_one_iff hS hA φ a).mpr hzero
  have hlog : ((modelPointPlace hS hA φ).valuation L (algebraMap A L a)).log < (0 : ℤ) := by
    simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
  omega

end Construction

end

end ProximityPrize.SubmissionLower.AffineModelPointLift
