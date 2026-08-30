import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z5
import ProximityPrize.SubmissionLower.AE
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransportResearch
open scoped Classical
open ContactFlagBezout6543Research
open ContactFlagAffineResidualAutomorphismResearch
open ContactIdentityResidualPrimeTransportResearch
open ContactResidualSparseComponentAdapterResearch
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
theorem originalAlgHom_eq_residualAlgHom
   (aY v bY aS bS cS:K):
   originalAlgHom aY v bY aS bS cS=
     residualAlgHom
       (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
       (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY)
       (-v⁻¹*bS*v⁻¹)
       (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [originalAlgHom,residualAlgHom,originalImage,residualImage] <;>
   ring
theorem polynomialInFlag_originalAlgHom
   (r:FlagDegree) (A:Poly3 K) (aY v bY aS bS cS:K)
   (hA:PolynomialInFlag r A):
   PolynomialInFlag r (originalAlgHom aY v bY aS bS cS A):=by
 rw [originalAlgHom_eq_residualAlgHom]
 exact ContactFlagAffineResidualAutomorphismResearch.polynomialInFlag_residualAlgHom
   r A _ _ _ _ _ _ hA
@[simp] theorem residual_original_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (A:Poly3 K):
   residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)=A:=by
 have h:=AlgHom.congr_fun
   (residual_comp_original aY v bY aS bS cS hv) A
 simpa only [AlgHom.comp_apply,AlgHom.id_apply] using h
theorem forwardResidualPoint_injective
   (aY v bY aS bS cS:K) (hv:v≠0):
   Function.Injective (forwardResidualPoint aY v bY aS bS cS):=by
 intro q r hqr
 have h0:=congrFun hqr 0
 have h1:=congrFun hqr 1
 have h2:=congrFun hqr 2
 simp only [forwardResidualPoint,Matrix.cons_val_zero,
   Matrix.cons_val_one,Matrix.cons_val_two] at h0 h1 h2
 change q 2=r 2 at h2
 have hy:q 0=r 0:=by
   apply (mul_left_cancel₀ hv)
   rw [h2] at h0
   linear_combination h0
 have hs:q 1=r 1:=by
   apply (mul_left_cancel₀ hv)
   rw [hy,h2] at h1
   linear_combination h1
 funext i
 fin_cases i
 · exact hy
 · exact hs
 · exact h2
theorem finiteZeroSetBound_map_residual
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P A cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     (residualAlgHom aY v bY aS bS cS A) cost:=by
 classical
 intro points hpointsP hpointsA
 let forward:=forwardResidualPoint aY v bY aS bS cS
 let oldPoints:=points.image forward
 have hcard:oldPoints.card=points.card:=by
   exact Finset.card_image_of_injective points
     (forwardResidualPoint_injective aY v bY aS bS cS hv)
 rw [←hcard]
 apply hzero oldPoints
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   exact (map_le_pointKernel_iff aY v bY aS bS cS hv P q).mp
     (hpointsP q hq)
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hz:=hpointsA q hq
   change MvPolynomial.eval q
     (residualAlgHom aY v bY aS bS cS A)=0 at hz
   change MvPolynomial.eval
     (forwardResidualPoint aY v bY aS bS cS q) A=0
   change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv A)=0 at hz
   rwa [eval_residualEquiv] at hz
theorem finiteZeroSetBound_map_residual_of_inverse
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (originalAlgHom aY v bY aS bS cS A) cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     A cost:=by
 have h:=finiteZeroSetBound_map_residual aY v bY aS bS cS hv P
   (originalAlgHom aY v bY aS bS cS A) cost hzero
 change FiniteZeroSetBound
   (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
   (residualAlgHom aY v bY aS bS cS
     (originalAlgHom aY v bY aS bS cS A)) cost at h
 rw [residual_original_apply aY v bY aS bS cS hv] at h
 exact h
structure PrimeFlagZeroBudget
   (P:Ideal (Poly3 K)) (cost:FlagDegree → ℕ) where
 zero_le:∀ (r:FlagDegree) (A:Poly3 K),
   PolynomialInFlag r A → A∉P → FiniteZeroSetBound P A (cost r)
def PrimeFlagZeroBudget.mapResidual
   {P:Ideal (Poly3 K)} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost)
   (aY v bY aS bS cS:K) (hv:v≠0):
   PrimeFlagZeroBudget
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     cost where
 zero_le:=by
   intro r A hA hproper
   have hAold:PolynomialInFlag r
       (originalAlgHom aY v bY aS bS cS A):=
     polynomialInFlag_originalAlgHom r A aY v bY aS bS cS hA
   have hproperOld:originalAlgHom aY v bY aS bS cS A∉P:=by
     intro hmem
     apply hproper
     have hmapped:=Ideal.mem_map_of_mem
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom hmem
     change residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)∈
         P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom
       at hmapped
     rwa [residual_original_apply aY v bY aS bS cS hv] at hmapped
   exact finiteZeroSetBound_map_residual_of_inverse
     aY v bY aS bS cS hv P A (cost r)
     (B.zero_le r _ hAold hproperOld)
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransportResearch
