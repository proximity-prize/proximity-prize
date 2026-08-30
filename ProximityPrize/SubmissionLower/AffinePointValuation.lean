import ProximityPrize.Benchmark.TargetLower
import Mathlib.NumberTheory.FunctionField

namespace ProximityPrize.SubmissionLower.AffinePointValuation

open IsDedekindDomain

noncomputable section

section PointKernels

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

def pointKernel (phi : S →ₐ[K] K) : Ideal S := RingHom.ker phi.toRingHom

@[simp] theorem mem_pointKernel (phi : S →ₐ[K] K) (s : S) :
    s ∈ pointKernel phi ↔ phi s = 0 := Iff.rfl

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

def parameterDifference (phi : S →ₐ[K] K) : S :=
  algebraMap (Polynomial K) S
    (Polynomial.X - Polynomial.C (phi (algebraMap (Polynomial K) S Polynomial.X)))

theorem parameterDifference_mem (phi : S →ₐ[K] K) :
    parameterDifference phi ∈ pointKernel phi := by
  have hconstant (c : K) :
      algebraMap (Polynomial K) S (Polynomial.C c) = algebraMap K S c :=
    (IsScalarTower.algebraMap_apply K (Polynomial K) S c).symm
  simp [parameterDifference, hconstant]

omit [IsScalarTower K (Polynomial K) S] in
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

def pointPlace (hinj : Function.Injective (algebraMap (Polynomial K) S))
    (phi : S →ₐ[K] K) : HeightOneSpectrum S :=
  ⟨pointKernel phi, RingHom.ker_isPrime phi.toRingHom, pointKernel_ne_bot hinj phi⟩

variable [Field L] [Algebra S L] [IsFractionRing S L]

end ActualPlaces

section ConcreteNormalization

variable (K L : Type*) [Field K] [Field L]
  [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
  [IsScalarTower (Polynomial K) (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

end ConcreteNormalization

end

end ProximityPrize.SubmissionLower.AffinePointValuation
