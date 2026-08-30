import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.EU
import ProximityPrize.SubmissionLower.I
import ProximityPrize.SubmissionLower.GJ
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily6600Research
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
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def regularComponentCurveStageOfSupport
   (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d support:=by
 classical
 let GammaC:=componentSeeds Omega G T (regularitySurface phi F) Gamma
   (selectedPoint phi selected) C
 have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T
   (regularitySurface phi F) Gamma (selectedPoint phi selected) C
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=G
   T:=T
   primeData:={
     ideal:=C.1
     isPrime:=inferInstance
     G_mem:=regularComponent_G_mem Omega G T (regularitySurface phi F) C
     T_mem:=regularComponent_T_mem Omega G T (regularitySurface phi F) C
     H_not_mem:=regularComponent_H_not_mem Omega G T
       (regularitySurface phi F) C
     ne_point:=regularComponent_ne_point Omega G T
       (regularitySurface phi F) C
   }
   G_dvd_surface:=hdiv
   G_flag_support:=hGflag
   T_flag_support:=hTflag
   surface_s_weight:=hFs
   surface_ys_weight:=hFys
   surface_total_weight:=hFtotal
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolution gamma (hsub hgamma)
   regular:=fun gamma hgamma↦hregular gamma (hsub hgamma)
   on_prime:=fun gamma hgamma↦componentSeeds_on_prime Omega G T
     (regularitySurface phi F) Gamma (selectedPoint phi selected) C gamma hgamma
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma GammaC d e
     hsub hnoPencil
   characteristic_bound:=hchar
 }
def activeDifferentialSupport:ResidualSupportParameters where
 s:=6
 ys:=33
 total:=582
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
def regularComponentCurveStageActive
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 6)
   (hFys:wt residualYSWeights F ≤ 33)
   (hFtotal:wt residualTotalWeights F ≤ 582)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d activeDifferentialSupport:=
 regularComponentCurveStageOfSupport activeDifferentialSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
def regularComponentCurveStage
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 8)
   (hFys:wt residualYSWeights F ≤ 43)
   (hFtotal:wt residualTotalWeights F ≤ 503)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d:=
 regularComponentCurveStageOfSupport ResidualSupportParameters.acceptedSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily6600Research
