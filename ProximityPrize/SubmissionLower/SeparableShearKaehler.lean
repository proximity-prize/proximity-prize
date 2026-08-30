import ProximityPrize.Benchmark.TargetLower
import Mathlib.RingTheory.Unramified.Field

namespace ProximityPrize.SubmissionLower.SeparableShearKaehler

open scoped Classical
open KaehlerDifferential

noncomputable section

set_option maxHeartbeats 2000000

section RatFuncDifferential

variable (K : Type*) [Field K]

theorem span_singleton_D_ratFunc_X :
    Submodule.span (RatFunc K)
        ({D K (RatFunc K)
          (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)} :
          Set Ω[RatFunc K⁄K]) = ⊤ := by
  have hall := span_range_map_derivation_of_isLocalization
    K (Polynomial K) (RatFunc K) (nonZeroDivisors (Polynomial K))
  apply top_unique
  rw [← hall]
  apply Submodule.span_le.mpr
  rintro x ⟨P, rfl⟩
  change map K K (Polynomial K) (RatFunc K) (D K (Polynomial K) P) ∈ _
  rw [polynomial_D_apply, LinearMap.map_smul_of_tower, map_D]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.subset_span (Set.mem_singleton _))

end RatFuncDifferential

section ProjectionCriterion

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def parameterDifferential (embedding : RatFunc K →ₐ[K] L) : Ω[L⁄K] :=
  D K L (embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))

theorem isSeparable_iff_span_parameterDifferential
    (embedding : RatFunc K →ₐ[K] L) :
    letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) L →
      (Algebra.IsSeparable (RatFunc K) L ↔
        Submodule.span L ({parameterDifferential K L embedding} : Set Ω[L⁄K]) = ⊤) := by
  letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (embedding.commutes c).symm
  intro hfinite
  letI : FiniteDimensional (RatFunc K) L := hfinite
  constructor
  · intro hsep
    letI : Algebra.IsSeparable (RatFunc K) L := hsep
    letI : Algebra.FormallyUnramified (RatFunc K) L :=
      Algebra.FormallyUnramified.of_isSeparable (RatFunc K) L
    have htarget : Subsingleton Ω[L⁄RatFunc K] := inferInstance
    have hsurj : Function.Surjective (mapBaseChange K (RatFunc K) L) := by
      rw [← LinearMap.range_eq_top, range_mapBaseChange]
      apply top_unique
      intro x _
      change map K (RatFunc K) L L x = 0
      exact Subsingleton.elim _ _
    have hsource := span_singleton_D_ratFunc_X K
    rw [← LinearMap.range_eq_top] at hsurj
    apply top_unique
    rw [← hsurj]
    rintro x ⟨x, rfl⟩
    induction x with
    | zero => simp
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    | tmul l ω =>
        have hω : ω ∈ Submodule.span (RatFunc K)
            ({D K (RatFunc K)
              (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)} :
              Set Ω[RatFunc K⁄K]) := by
          rw [hsource]
          trivial
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hω
        rw [TensorProduct.tmul_smul]
        change mapBaseChange K (RatFunc K) L
          ((algebraMap (RatFunc K) L a * l) ⊗ₜ
            D K (RatFunc K)
              (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) ∈ _
        rw [mapBaseChange_tmul, map_D]
        change (algebraMap (RatFunc K) L a * l) •
          parameterDifferential K L embedding ∈
            Submodule.span L
              ({parameterDifferential K L embedding} : Set Ω[L⁄K])
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_singleton _))
  · intro hspan
    have hrange : LinearMap.range (mapBaseChange K (RatFunc K) L) = ⊤ := by
      apply top_unique
      rw [← hspan]
      apply Submodule.span_le.mpr
      intro η hη
      rw [Set.mem_singleton_iff.mp hη]
      refine ⟨1 ⊗ₜ D K (RatFunc K)
          (algebraMap (Polynomial K) (RatFunc K) Polynomial.X), ?_⟩
      rw [mapBaseChange_tmul, one_smul, map_D]
      rfl
    have hker : LinearMap.ker (map K (RatFunc K) L L) = ⊤ := by
      rw [← range_mapBaseChange]
      exact hrange
    have hzero : map K (RatFunc K) L L = 0 := by
      apply LinearMap.ker_eq_top.mp hker
    have hsub : Subsingleton Ω[L⁄RatFunc K] := by
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := map_surjective K (RatFunc K) L x
      obtain ⟨y, rfl⟩ := map_surjective K (RatFunc K) L y
      rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]
    letI : Subsingleton Ω[L⁄RatFunc K] := hsub
    letI : Algebra.FormallyUnramified (RatFunc K) L := ⟨inferInstance⟩
    exact Algebra.FormallyUnramified.isSeparable (RatFunc K) L

end ProjectionCriterion

end

end ProximityPrize.SubmissionLower.SeparableShearKaehler
