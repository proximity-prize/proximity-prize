/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Matthew Jasper,Kevin Buzzard
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Ideal_IsPrincipal
section ProximityFlatProofPort
open Function (Injective Surjective)
open LinearMap (lsmul rTensor lTensor)
open Submodule (IsPrincipal torsion)
open TensorProduct
namespace Module.Flat
section Semiring
variable {R M:Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
open LinearMap in
lemma isSMulRegular_of_isRegular {r:R} (hr:IsRegular r) [Flat R M]:
    IsSMulRegular M r:=by
  have h:=Flat.rTensor_preserves_injective_linearMap (M:=M)
    (toSpanSingleton R R r) <| hr.right
  have h2:(fun (x:M)↦r • x)=
      (TensorProduct.lid R M).toLinearMap.comp
        ((rTensor M (toSpanSingleton R R r)).comp
          (TensorProduct.lid R M).symm.toLinearMap):=by ext;simp
  rw [IsSMulRegular,h2]
  simp [h,LinearEquiv.injective]
instance isTorsionFree [Flat R M]:IsTorsionFree R M:=
  ⟨fun _ hr↦isSMulRegular_of_isRegular hr⟩
end Semiring
section Ring
variable {R M:Type*} [CommRing R] [AddCommGroup M] [Module R M]
open scoped nonZeroDivisors
open LinearMap in
lemma isSMulRegular_of_nonZeroDivisors {r:R} (hr:r∈R⁰) [Flat R M]:IsSMulRegular M r:=by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r,hr⟩
theorem torsion_eq_bot [Flat R M]:torsion R M=⊥:=by
  rw [eq_bot_iff]
  rintro m ⟨⟨r,hr⟩,h⟩
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)
@[stacks 0539 "Generalized valuation ring to Bezout domain"]
theorem flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R]:
    Flat R M ↔ torsion R M=⊥:=by
  refine ⟨fun _↦torsion_eq_bot,?_⟩
  intro htors
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  obtain (rfl | h):=eq_or_ne I ⊥
  · rintro x y-
    apply Subsingleton.elim
  ·
    have hprinc:I.IsPrincipal:=IsBezout.isPrincipal_of_FG I hFG
    have:IsPrincipal.generator I≠0:=by
      rwa [ne_eq, ←IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [←LinearEquiv.coe_toLinearMap, ←LinearMap.coe_comp,LinearEquiv.coe_rTensor,rTensor,
      lift_comp_map,LinearMap.compl₂_id,LinearMap.comp_assoc,
      Ideal.subtype_isoBaseOfIsPrincipal_eq_mul,LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul,
      LinearMap.coe_comp]
    rw [←Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [←Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert! Function.injective_id
    ext
    simp
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain R]
    (h:∀ (P:Ideal R),[P.IsMaximal] → ValuationRing (Localization P.primeCompl)):
    Flat R M ↔ torsion R M=⊥:=by
  refine ⟨fun _↦Flat.torsion_eq_bot,fun h↦?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [←Submodule.isTorsionFree_iff_torsion_eq_bot] at h
  rw [←flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl,
    Flat.flat_iff_torsion_eq_bot_of_isBezout, ←Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance
@[stacks 0AUW "(1)"]
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot [IsDedekindDomain R]:
    Flat R M ↔ torsion R M=⊥:=by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P↦inferInstance
instance [IsDedekindDomain R] [IsTorsionFree R M]:Flat R M:=by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ←Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance
end Ring
end Module.Flat
