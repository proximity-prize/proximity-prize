import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import ProximityPrize.SubmissionLower.R6961MarkedResidueRows
import Mathlib.RingTheory.Valuation.LocalSubring

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace Lower6961.MarkedEvaluation
open Polynomial IsLocalRing
open scoped Polynomial
variable (K Ω:Type) [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
local notation "j" => algebraMap (Polynomial K) (RatFunc K)
local notation "ι" => algebraMap (RatFunc K) Ω

/-- A place in the one common splitting field, including its residue map on
the entire scalar polynomial ring, with no unramifiedness hypothesis. -/
structure MarkPlace (z:K) where
  V : ValuationSubring Ω
  lift : (Polynomial K)→+*V
  value : ∀p,(lift p:Ω)=ι (j p)
  specialize : ∀p,residue V (lift p)=residue V (lift (C (p.eval z)))

def markPlace (z:K) : MarkPlace K Ω z := by
  apply Classical.choice
  let P:=RingHom.ker (evalRingHom z)
  letI : P.IsPrime:=RingHom.ker_isPrime _
  let A:=Localization.AtPrime P
  let b:=algebraMap (Polynomial K) A
  let f: A→+*Ω:=(algebraMap (RatFunc K) Ω).comp (Lower6960.CollisionTame.branchFractionHom P)
  obtain ⟨V,h,loc⟩:=IsLocalRing.exists_factor_valuationRing f
  let g:A→+*V:=f.codRestrict V.toSubring h
  let l:=g.comp b
  have hπ:residue V (l (Polynomial.X-C z))=0 := by
    apply (residue_eq_zero_iff _).mpr
    change ¬IsUnit (g (b (Polynomial.X-C z)))
    intro u
    have nu:¬IsUnit (b (Polynomial.X-C z)) := by
      intro bunit
      have outside:Polynomial.X-C z ∈ P.primeCompl :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A P _).mp bunit
      apply outside
      change (Polynomial.X-C z).eval z=0
      rw [eval_sub,eval_X,eval_C,sub_self]
    exact nu (IsUnit.of_map g _ u)
  refine ⟨⟨V,l,fun p=>congrArg (algebraMap (RatFunc K) Ω) (Lower6960.CollisionTame.branchFractionHom_apply _ _),fun p=>?_⟩⟩
  have reducing : ((residue V).comp l)=(((residue V).comp l).comp C).comp (evalRingHom z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,coe_evalRingHom,eval_C]
    · change residue V (l Polynomial.X)=residue V (l (C (Polynomial.X.eval z)))
      rw [eval_X];rwa [map_sub,map_sub,sub_eq_zero] at hπ
  exact DFunLike.congr_fun reducing p

namespace MarkPlace
variable {K Ω} {z:K} (P:MarkPlace K Ω z)
def pi := P.lift (Polynomial.X-C z)
theorem pi_ne : P.pi≠0 := by
  intro h
  have exactValue:=P.value (Polynomial.X-C z)
  rw [show P.lift (Polynomial.X-C z)=0 from h] at exactValue
  exact ((map_ne_zero_iff _ (algebraMap (RatFunc K) Ω).injective).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr (X_sub_C_ne_zero z))) exactValue.symm
theorem pi_residue : residue P.V P.pi=0 := by
  have hz:((Polynomial.X:(Polynomial K))-C z).eval z=0 := by simp
  rw [pi,P.specialize,hz,map_zero,map_zero,map_zero]
theorem lift_unit {p:(Polynomial K)} (nz:p.eval z≠0) : IsUnit (P.lift p) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [P.specialize]
  exact (map_ne_zero_iff _ (((residue P.V).comp P.lift).comp (C:K→+*(Polynomial K))).injective).mpr nz
theorem separable {q:(Polynomial (Polynomial K))} (sep:(q.map (evalRingHom z)).Separable) :
    ((q.map P.lift).map (residue P.V)).Separable := by
  have eq : (residue P.V).comp P.lift=((((residue P.V).comp P.lift).comp C).comp (evalRingHom z)) :=
    RingHom.ext P.specialize
  rw [Polynomial.map_map,eq,←Polynomial.map_map]
  exact sep.map

/-- Integral entries and all their conjugates land in the selected local ring. -/
theorem integral_mem [Algebra (Polynomial K) Ω] [IsScalarTower (Polynomial K) (RatFunc K) Ω]
    {x:Ω} (hx:IsIntegral (Polynomial K) x) : x∈P.V := by
  letI : Algebra (Polynomial K) P.V:=P.lift.toAlgebra
  letI : IsScalarTower (Polynomial K) P.V Ω:=IsScalarTower.of_algebraMap_eq (fun a=>
    (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) Ω a).trans (P.value a).symm)
  obtain ⟨v,hv⟩:=IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A:=P.V))
  exact hv ▸ v.property
end MarkPlace

#print axioms markPlace
#print axioms MarkPlace.integral_mem
end Lower6961.MarkedEvaluation
