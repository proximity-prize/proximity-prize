import ProximityPrize.SubmissionLower.ArbitraryRationalProjection
import ProximityPrize.SubmissionLower.SeparableShearKaehler

namespace ProximityPrize.SubmissionLower.GlobalSeparableShear

open scoped Classical TensorProduct
open Polynomial KaehlerDifferential
open SeparableShearKaehler
open ArbitraryRationalProjection

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

theorem eq_algebraMap_of_isAlgebraic [IsAlgClosed K]
    (s : L) (hs : IsAlgebraic K s) :
    ∃ c : K, algebraMap K L c = s := by
  let S : IntermediateField K L := IntermediateField.adjoin K {s}
  letI : Algebra.IsAlgebraic K S :=
    IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := S)).2
      (⟨s, IntermediateField.mem_adjoin_simple_self K s⟩ : S)
  refine ⟨c, ?_⟩
  have hcast := congrArg (algebraMap S L) hc
  simpa only [IntermediateField.algebraMap_apply,
    IntermediateField.coe_algebraMap_apply] using hcast

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

theorem shear_bad_coefficient_subsingleton
    (r z : L) (hdz : D K L z ≠ 0) :
    ∀ {a b : K},
      D K L r + a • D K L z = 0 →
      D K L r + b • D K L z = 0 → a = b := by
  intro a b ha hb
  apply smul_left_injective K hdz
  exact (eq_neg_of_add_eq_zero_right ha).trans
    (eq_neg_of_add_eq_zero_right hb).symm

section FiniteFamily

variable {I : Type*} [Fintype I]
variable (E : I → Type*) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
variable (r z : ∀ i, E i)

end FiniteFamily

end

end ProximityPrize.SubmissionLower.GlobalSeparableShear
