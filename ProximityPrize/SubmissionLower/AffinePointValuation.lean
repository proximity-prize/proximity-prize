import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_FunctionField



/-! .
















 -/

namespace ProximityPrize.SubmissionLower.AffinePointValuation

open IsDedekindDomain

noncomputable section

section PointKernels

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- . -/
def pointKernel (phi : S →ₐ[K] K) : Ideal S := RingHom.ker phi.toRingHom

@[simp] theorem mem_pointKernel (phi : S →ₐ[K] K) (s : S) :
    s ∈ pointKernel phi ↔ phi s = 0 := Iff.rfl

theorem point_surjective (phi : S →ₐ[K] K) : Function.Surjective phi := by
  intro c
  exact ⟨algebraMap K S c, by simpa using phi.commutes c⟩

theorem pointKernel_isPrime (phi : S →ₐ[K] K) : (pointKernel phi).IsPrime :=
  RingHom.ker_isPrime phi.toRingHom

theorem pointKernel_isMaximal (phi : S →ₐ[K] K) : (pointKernel phi).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective phi.toRingHom (point_surjective phi)

/-- . -/
theorem pointKernel_injective :
    Function.Injective (pointKernel : (S →ₐ[K] K) → Ideal S) := by
  intro phi psi hker
  apply AlgHom.ext
  intro s
  have hs : s - algebraMap K S (phi s) ∈ pointKernel phi := by simp
  have hs' : s - algebraMap K S (phi s) ∈ pointKernel psi := hker ▸ hs
  have hz := (mem_pointKernel psi _).mp hs'
  have heq : psi s = phi s := sub_eq_zero.mp (by simpa using hz)
  exact heq.symm

variable [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]

/-- . -/
def parameterDifference (phi : S →ₐ[K] K) : S :=
  algebraMap (Polynomial K) S
    (Polynomial.X - Polynomial.C (phi (algebraMap (Polynomial K) S Polynomial.X)))

theorem parameterDifference_mem (phi : S →ₐ[K] K) :
    parameterDifference phi ∈ pointKernel phi := by
  have hconstant (c : K) :
      algebraMap (Polynomial K) S (Polynomial.C c) = algebraMap K S c :=
    (IsScalarTower.algebraMap_apply K (Polynomial K) S c).symm
  simp [parameterDifference, hconstant]

theorem parameterDifference_ne_zero
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) : parameterDifference phi ≠ 0 := by
  intro hz
  apply Polynomial.X_sub_C_ne_zero (phi (algebraMap (Polynomial K) S Polynomial.X))
  apply hinj
  simpa only [parameterDifference, map_zero] using hz

theorem pointKernel_ne_bot
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) : pointKernel phi ≠ ⊥ := by
  intro hbot
  have hzero : parameterDifference phi = 0 := by
    simpa [hbot] using parameterDifference_mem phi
  exact parameterDifference_ne_zero hinj phi hzero

end PointKernels

section ActualPlaces

variable {K S L : Type*} [Field K] [CommRing S] [IsDedekindDomain S]
  [Algebra K S] [Algebra (Polynomial K) S] [IsScalarTower K (Polynomial K) S]

/-- . -/
def pointPlace (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) : HeightOneSpectrum S :=
  ⟨pointKernel phi, pointKernel_isPrime phi, pointKernel_ne_bot hinj phi⟩

@[simp] theorem pointPlace_asIdeal
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) : (pointPlace hinj phi).asIdeal = pointKernel phi := rfl

theorem pointPlace_injective
    (hinj : Function.Injective (algebraMap (Polynomial K) S)) :
    Function.Injective (pointPlace hinj : (S →ₐ[K] K) → HeightOneSpectrum S) := by
  intro phi psi h
  apply pointKernel_injective
  exact congrArg HeightOneSpectrum.asIdeal h

variable [Field L] [Algebra S L] [IsFractionRing S L]

theorem point_valuation_lt_one_iff
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) (h : S) :
    (pointPlace hinj phi).valuation L (algebraMap S L h) < 1 ↔ phi h = 0 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact mem_pointKernel phi h

/-- .
 -/
theorem point_zero_order_ge_one
    (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) (h : S) (hne : h ≠ 0) (hzero : phi h = 0) :
    1 ≤ -((pointPlace hinj phi).valuation L (algebraMap S L h)).log := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hv0 := (pointPlace hinj phi).intValuation_ne_zero h hne
  have hvlt : (pointPlace hinj phi).intValuation h < 1 :=
    ((pointPlace hinj phi).intValuation_lt_one_iff_mem h).2 hzero
  have hlog : ((pointPlace hinj phi).intValuation h).log < (0 : ℤ) := by
    simpa using (WithZero.log_lt_log hv0 (by simp)).2 hvlt
  omega

end ActualPlaces

section ConcreteNormalization

variable (K L : Type*) [Field K] [Field L]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

/-- . -/
abbrev ActualNormalization := FunctionField.ringOfIntegers K L

/-- . -/
local instance normalizationScalarAlgebra : Algebra K (ActualNormalization K L) :=
  ((algebraMap (Polynomial K) (ActualNormalization K L)).comp
    (Polynomial.C : K →+* Polynomial K)).toAlgebra

local instance normalizationScalarTower :
    IsScalarTower K (Polynomial K) (ActualNormalization K L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem actual_normalization_finite :
    Module.Finite (Polynomial K) (ActualNormalization K L) :=
  IsIntegralClosure.finite (Polynomial K) (RatFunc K) L (ActualNormalization K L)

theorem actual_normalization_dedekind : IsDedekindDomain (ActualNormalization K L) :=
  inferInstance

theorem actual_normalization_fractionField : IsFractionRing (ActualNormalization K L) L :=
  inferInstance

theorem actual_normalization_base_injective :
    Function.Injective (algebraMap (Polynomial K) (ActualNormalization K L)) :=
  FunctionField.ringOfIntegers.algebraMap_injective K L

/-- . -/
def normalizationPointPlace (phi : ActualNormalization K L →ₐ[K] K) :
    HeightOneSpectrum (ActualNormalization K L) :=
  pointPlace (actual_normalization_base_injective K L) phi

theorem normalizationPointPlace_injective :
    Function.Injective (normalizationPointPlace K L) :=
  pointPlace_injective (actual_normalization_base_injective K L)

/-- .
 -/
theorem normalization_point_zero_order_ge_one
    (phi : ActualNormalization K L →ₐ[K] K) (h : ActualNormalization K L)
    (hne : h ≠ 0) (hzero : phi h = 0) :
    1 ≤ -((normalizationPointPlace K L phi).valuation L
      (algebraMap (ActualNormalization K L) L h)).log :=
  point_zero_order_ge_one (L := L) (actual_normalization_base_injective K L)
    phi h hne hzero

end ConcreteNormalization

end


end ProximityPrize.SubmissionLower.AffinePointValuation
