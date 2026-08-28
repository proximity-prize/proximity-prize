import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ArbitraryRationalProjectionResearch
import ProximityPrize.SubmissionLower.SeparableShearTranscendenceResearch

/-!
# One separating shear coefficient for a finite component family

For every component on which `Z` is a finite separable parameter, at most
one base-field scalar `lambda` can make `d(R + lambda * Z)` vanish.  Over an
algebraically closed (hence infinite) base, one nonzero `lambda` therefore
works simultaneously for any finite family.

This file also proves the nonvanishing fact hidden by a mere
`span {dZ} = top` statement.  A finite separable field extension is formally
etale; base change then carries the visibly nonzero `dX` of the rational
function field to `dZ`.
-/

namespace ProximityPrize.SubmissionLower.GlobalSeparableShearResearch

open scoped Classical TensorProduct
open Polynomial KaehlerDifferential
open SeparableShearKaehlerResearch
open SeparableShearTranscendenceResearch
open ArbitraryRationalProjectionResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/- This is the finite-dimensional specialization of Iversen II.5.3.  The
proof is the standard simple-extension lifting argument used by Mathlib's
`RingTheory.Etale.Field`; keeping the finite hypothesis avoids importing the
unavailable infinite separable-extension gluing layer. -/
theorem formallyEtale_of_finite_isSeparable
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Algebra.FormallyEtale F E := by
  have := Algebra.FormallyUnramified.of_isSeparable F E
  have := Algebra.FormallyUnramified.finite_of_free (R := F) (S := E)
  refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_
  refine ⟨Algebra.FormallyUnramified.iff_comp_injective_of_small.mp
    (Algebra.FormallyUnramified.of_isSeparable F E) I h, ?_⟩
  intro f
  let pb := Field.powerBasisOfFiniteOfSeparable F E
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
  have helper : ∀ x, IsScalarTower.toAlgHom F B
      (HasQuotient.Quotient B I) x =
      Ideal.Quotient.mk I x := fun _ ↦ rfl
  have hx' : Ideal.Quotient.mk I (aeval x (minpoly F pb.gen)) = 0 := by
    rw [← helper, ← aeval_algHom_apply, helper, hx, aeval_algHom_apply,
      minpoly.aeval, map_zero]
  obtain ⟨u, hu⟩ : ∃ u,
      (aeval x) (derivative (minpoly F pb.gen)) * u + 1 ∈ I := by
    have hunit := (isUnit_iff_ne_zero.mpr
      ((Algebra.IsSeparable.isSeparable F pb.gen).aeval_derivative_ne_zero
        (minpoly.aeval F _))).map f
    rw [← aeval_algHom_apply, ← hx, ← helper, aeval_algHom_apply,
      helper] at hunit
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective
      (-hunit.unit⁻¹ : HasQuotient.Quotient B I)
    use u
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_one, hu,
      mul_neg, IsUnit.mul_val_inv, neg_add_cancel]
  use pb.liftEquiv.symm ⟨x + u * aeval x (minpoly F pb.gen), ?_⟩
  · apply pb.algHom_ext
    simp [hx, hx']
  · rw [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero,
      derivative_map, ← one_mul (eval x _), eval_map_algebraMap,
      eval_map_algebraMap, ← mul_assoc, ← add_mul, ← Ideal.mem_bot,
      ← h, pow_two, add_comm]
    · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    rw [← Ideal.mem_bot, ← h]
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hx', mul_zero]

/-- The rational variable has a genuinely nonzero absolute differential. -/
theorem ratFunc_variableDifferential_ne_zero (K : Type*) [Field K] :
    D K (RatFunc K)
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ≠ 0 := by
  letI : Algebra.FormallyEtale (Polynomial K) (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Polynomial K))
  intro hzero
  have htensor := congrArg
    (tensorKaehlerEquivOfFormallyEtale
      K (Polynomial K) (RatFunc K)).symm hzero
  have htensor' : (1 : RatFunc K) ⊗ₜ[Polynomial K]
      D K (Polynomial K) Polynomial.X = 0 := by
    simpa only [map_zero,
      tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
  let l : Ω[Polynomial K⁄K] →ₗ[Polynomial K] RatFunc K :=
    (Algebra.linearMap (Polynomial K) (RatFunc K)).comp
      (polynomialEquiv K).toLinearMap
  have himage := congrArg (l.liftBaseChange (RatFunc K)) htensor'
  have hone : (1 : RatFunc K) = 0 := by
    rw [LinearMap.liftBaseChange_tmul, one_smul, map_zero] at himage
    change algebraMap (Polynomial K) (RatFunc K)
      (polynomialEquiv K (D K (Polynomial K) Polynomial.X)) = 0 at himage
    simpa only [polynomialEquiv_D, derivative_X, map_one] using himage
  exact one_ne_zero hone

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- A finite separable rational projection has nonzero parameter
differential.  This is stronger than, and complements, the earlier span
criterion. -/
theorem parameterDifferential_ne_zero_of_isSeparable
    (embedding : RatFunc K →ₐ[K] L)
    (hfinite :
      letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hsep :
      letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) L) :
    parameterDifferential K L embedding ≠ 0 := by
  letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (embedding.commutes c).symm
  letI : FiniteDimensional (RatFunc K) L := hfinite
  letI : Algebra.IsSeparable (RatFunc K) L := hsep
  letI : Algebra.FormallyEtale (RatFunc K) L :=
    formallyEtale_of_finite_isSeparable (RatFunc K) L
  intro hzero
  change D K L
    (algebraMap (RatFunc K) L
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = 0 at hzero
  have htensor := congrArg
    (tensorKaehlerEquivOfFormallyEtale K (RatFunc K) L).symm hzero
  have htensor' : (1 : L) ⊗ₜ[RatFunc K]
      D K (RatFunc K)
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = 0 := by
    simpa only [map_zero,
      tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
  have hsource : D K (RatFunc K)
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = 0 := by
    rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at htensor'
    exact htensor'
  exact ratFunc_variableDifferential_ne_zero K hsource

/-- For a nonzero direction vector, the affine differential equation has
at most one solution in the base-field coefficient. -/
theorem shear_bad_coefficient_subsingleton
    (r z : L) (hdz : D K L z ≠ 0) :
    ∀ {a b : K},
      D K L r + a • D K L z = 0 →
      D K L r + b • D K L z = 0 → a = b := by
  intro a b ha hb
  apply smul_left_injective K hdz
  exact (eq_neg_of_add_eq_zero_right ha).trans
    (eq_neg_of_add_eq_zero_right hb).symm

/-- Once a scalar avoids differential cancellation, the corresponding
shear is a legitimate finite separable rational parameter. -/
theorem shear_transcendental_finite_separable_of_differential_ne_zero
    [IsAlgClosed K]
    (embeddingZ : RatFunc K →ₐ[K] L) (r z : L) (a : K)
    (hvalueZ : embeddingZ
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = z)
    (hfiniteZ :
      letI : Algebra (RatFunc K) L := embeddingZ.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hsepZ :
      letI : Algebra (RatFunc K) L := embeddingZ.toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) L)
    (hdiff : D K L r + a • D K L z ≠ 0) :
    ∃ hs : Transcendental K (r + a • z),
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L (r + a • z) hs).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc K) L) ∧
      (letI : Algebra (RatFunc K) L :=
          (elementEmbedding K L (r + a • z) hs).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc K) L) := by
  have hDs : D K L (r + a • z) = D K L r + a • D K L z := by
    rw [map_add, (D K L).map_smul]
  have hs : Transcendental K (r + a • z) := by
    show ¬ IsAlgebraic K _
    intro halg
    obtain ⟨c, hc⟩ := eq_algebraMap_of_isAlgebraic K L _ halg
    apply hdiff
    rw [← hDs, ← hc]
    exact (D K L).map_algebraMap c
  refine ⟨hs, ?_, ?_⟩
  · exact finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
      (r + a • z) hs
  · let embeddingS := elementEmbedding K L (r + a • z) hs
    have hfiniteS := finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
      (r + a • z) hs
    have hcriterionZ :=
      isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
    have hcriterionS :=
      isSeparable_iff_span_parameterDifferential K L embeddingS hfiniteS
    have hspanZ : Submodule.span L ({D K L z} : Set Ω[L⁄K]) = ⊤ := by
      have hz := hcriterionZ.mp hsepZ
      unfold parameterDifferential at hz
      rw [hvalueZ] at hz
      exact hz
    apply hcriterionS.mpr
    have hparamS : parameterDifferential K L embeddingS =
        D K L (r + a • z) := by
      unfold parameterDifferential embeddingS
      rw [elementEmbedding_variable]
    rw [hparamS, hDs]
    apply top_unique
    rw [← hspanZ]
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    have hS_mem : D K L r + a • D K L z ∈
        Submodule.span L ({D K L z} : Set Ω[L⁄K]) := by
      rw [hspanZ]
      trivial
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hS_mem
    have hb0 : b ≠ 0 := by
      intro hzero
      apply hdiff
      rw [← hb, hzero, zero_smul]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b⁻¹, ?_⟩
    rw [← hb, smul_smul, inv_mul_cancel₀ hb0, one_smul]

section FiniteFamily

variable {I : Type*} [Fintype I]
variable (E : I → Type*) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
variable (r z : ∀ i, E i)

/-- A single nonzero base-field coefficient avoids differential
cancellation on every member of a finite family. -/
theorem exists_common_nonzero_shear_coefficient
    [Infinite K] (hdz : ∀ i, D K (E i) (z i) ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∀ i,
      D K (E i) (r i) + a • D K (E i) (z i) ≠ 0 := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq I := Classical.decEq I
  let Bad : I → K → Prop := fun i a ↦
    D K (E i) (r i) + a • D K (E i) (z i) = 0
  have hsingle : ∀ i {a b}, Bad i a → Bad i b → a = b := by
    intro i a b ha hb
    exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
      (hdz i) ha hb
  let forbidden : Finset K := Finset.univ.biUnion fun i ↦
    if h : ∃ a, Bad i a then {Classical.choose h} else ∅
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (insert 0 forbidden)
  refine ⟨a, ?_, ?_⟩
  · intro hzero
    exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
  · intro i hbad
    have hex : ∃ b, Bad i b := ⟨a, hbad⟩
    let b := Classical.choose hex
    have hbbad : Bad i b := Classical.choose_spec hex
    have heq : a = b := hsingle i hbad hbbad
    have hbmem : b ∈ forbidden := by
      change b ∈ Finset.univ.biUnion (fun i ↦
        if h : ∃ a, Bad i a then {Classical.choose h} else ∅)
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa only [dif_pos hex, Finset.mem_singleton, b]
    exact ha (Finset.mem_insert_of_mem (heq ▸ hbmem))

/-- Fully packaged finite-family theorem: from finite separable `Z`
projections, choose one nonzero scalar such that every `R + a·Z` projection
is transcendental, finite, and separable. -/
theorem exists_common_finite_separable_shear
    [IsAlgClosed K]
    (embeddingZ : ∀ i, RatFunc K →ₐ[K] E i)
    (hvalueZ : ∀ i, embeddingZ i
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = z i)
    (hfiniteZ : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (embeddingZ i).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (E i))
    (hsepZ : ∀ i,
      letI : Algebra (RatFunc K) (E i) :=
        (embeddingZ i).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (E i)) :
    ∃ a : K, a ≠ 0 ∧ ∀ i,
      ∃ hs : Transcendental K (r i + a • z i),
        (letI : Algebra (RatFunc K) (E i) :=
            (elementEmbedding K (E i) (r i + a • z i) hs).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (E i)) ∧
        (letI : Algebra (RatFunc K) (E i) :=
            (elementEmbedding K (E i) (r i + a • z i) hs).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (E i)) := by
  have hdz : ∀ i, D K (E i) (z i) ≠ 0 := by
    intro i
    have h := parameterDifferential_ne_zero_of_isSeparable
      K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
    unfold parameterDifferential at h
    rw [hvalueZ i] at h
    exact h
  obtain ⟨a, ha0, hdiff⟩ :=
    exists_common_nonzero_shear_coefficient K E r z hdz
  refine ⟨a, ha0, fun i ↦ ?_⟩
  exact shear_transcendental_finite_separable_of_differential_ne_zero
    K (E i) (embeddingZ i) (r i) (z i) a
      (hvalueZ i) (hfiniteZ i) (hsepZ i) (hdiff i)

end FiniteFamily

end

end ProximityPrize.SubmissionLower.GlobalSeparableShearResearch

#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.formallyEtale_of_finite_isSeparable
#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.ratFunc_variableDifferential_ne_zero
#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.parameterDifferential_ne_zero_of_isSeparable
#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.exists_common_nonzero_shear_coefficient
#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.shear_transcendental_finite_separable_of_differential_ne_zero
#print axioms ProximityPrize.SubmissionLower.GlobalSeparableShearResearch.exists_common_finite_separable_shear
