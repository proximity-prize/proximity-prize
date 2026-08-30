import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ER
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research
open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveTerminalIncidenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactStratifiedResidualComponentAdapter6600Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactNearPencil6600FlagResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (support:ResidualSupportParameters)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hallPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.allCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag support.agreementDirection+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag cutFlag unitZFlag+
           flagMixed surfaceFlag cutFlag unitAllFlag):=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let degreeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost support.agreementDirection C
 let unitCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost unitYZFlag C
 let largeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.zCost C+B.allCost C
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-d) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-d)*largeCost C:=by
   intro C
   let GammaC:=componentSeeds Omega G T H Gamma
     (selectedPoint phi selected) C
   let S:=regularComponentCurveStageOfSupport support F G T selected Gamma
     nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
     hFs hFys hFtotal hinj
     hdegreeSelected hsolution hregular hnoPencil hchar C
   have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   apply recursive_curve_stratified_incidence_of_prime_flag_budget
     hphi S (fun r↦B.weightedCost r C) (B.primeBudget C)
     (degreeCost C) (unitCost C) U V (largeCost C)
   · intro t
     simpa only [degreeCost,unitCost] using
       B.weightedCost_supportResidualAgreementFlag support C t
   · exact hda
   · intro gamma hgamma
     exact hagreement gamma (hsub hgamma)
   · intro D hmany
     have hcard:GammaC.card ≤ e+1:=
       D.stage.card_le_pencil_of_many_identities hmany
     have hlargePositive:1 ≤ largeCost C:=by
       exact (hallPositive C).trans (Nat.le_add_left _ _)
     have hscaled:GammaC.card*(a-d) ≤ (e+1)*(a-d):=
       Nat.mul_le_mul_right (a-d) hcard
     have hcharged:(e+1)*(a-d) ≤
         (e+1)*(a-d)*largeCost C:=by
       have hmul:=Nat.mul_le_mul_left ((e+1)*(a-d)) hlargePositive
       simpa only [Nat.mul_one] using hmul
     exact hscaled.trans hcharged
   · simpa only [S,regularComponentCurveStageOfSupport] using hdegree
   · simpa only [S,regularComponentCurveStageOfSupport] using hunit
 have hlargeSum:
     (∑ C:RegularComponent Omega G T H,largeCost C) ≤
       flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitAllFlag:=by
   calc
     (∑ C:RegularComponent Omega G T H,largeCost C)=
         (∑ C:RegularComponent Omega G T H,B.zCost C)+
           ∑ C:RegularComponent Omega G T H,B.allCost C:=by
       simp only [largeCost,Finset.sum_add_distrib]
     _ ≤ flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitAllFlag:=
       Nat.add_le_add B.sum_zCost_le B.sum_allCost_le
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
   (flagMixed surfaceFlag cutFlag support.agreementDirection)
   (flagMixed surfaceFlag cutFlag unitYZFlag)
   (flagMixed surfaceFlag cutFlag unitZFlag+
     flagMixed surfaceFlag cutFlag unitAllFlag)
   degreeCost unitCost largeCost hcomponent
   (by simpa only [degreeCost] using
     B.sum_weightedCost_le support.agreementDirection)
   (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
   hlargeSum
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 8)
   (hFys:wt residualYSWeights F ≤ 43)
   (hFtotal:wt residualTotalWeights F ≤ 503)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hallPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.allCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag agreementDirection6600+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag cutFlag unitZFlag+
           flagMixed surfaceFlag cutFlag unitAllFlag):=by
 simpa only [ResidualSupportParameters.acceptedSupport,
   ResidualSupportParameters.agreementDirection,agreementDirection6600] using
   proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
     hphi F G T selected Gamma nodes x u0 u1 p e d a U V surfaceFlag cutFlag
     ResidualSupportParameters.acceptedSupport hdiv hGflag hTflag
     hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hGpoint hTpoint
     hagreement hnoPencil hchar hda B hallPositive hdegree hunit
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research
