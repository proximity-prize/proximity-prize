import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily
import ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout
open ContactIdentityResidualCurveIteration
open ContactIdentityResidualGlobalFlag
open ContactIdentityResidualZeroBudgetTransport
open ContactPrimeFlagBudgetFamily
open ContactStratifiedResidualComponentAdapter
open ContactPost6464MinkowskiRecurrence
open ContactResidualSupportParameters

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

def regularComponentCurveStageOfSupport
    (support : ResidualSupportParameters)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d : ℕ) [CharP Omega p] (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ support.s)
    (hFys : wt residualYSWeights F ≤ support.ys)
    (hFtotal : wt residualTotalWeights F ≤ support.total)
    (hinj : Set.InjOn x nodes)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ d)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hnoPencil : NoLargeSelectedPencil selected Gamma d e)
    (hchar : d < p)
    (C : RegularComponent Omega G T (regularitySurface phi F)) :
    CurveResidualStage phi
      (componentSeeds Omega G T (regularitySurface phi F) Gamma
        (selectedPoint phi selected) C)
      x p e surfaceFlag cutFlag d support := by
  classical
  let GammaC := componentSeeds Omega G T (regularitySurface phi F) Gamma
    (selectedPoint phi selected) C
  have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T
    (regularitySurface phi F) Gamma (selectedPoint phi selected) C
  exact {
    nodes := nodes
    u0 := u0
    u1 := u1
    selected := selected
    F := F
    G := G
    T := T
    primeData := {
      ideal := C.1
      isPrime := inferInstance
      G_mem := regularComponent_G_mem Omega G T (regularitySurface phi F) C
      T_mem := regularComponent_T_mem Omega G T (regularitySurface phi F) C
      H_not_mem := regularComponent_H_not_mem Omega G T
        (regularitySurface phi F) C
      ne_point := regularComponent_ne_point Omega G T
        (regularitySurface phi F) C
    }
    G_dvd_surface := hdiv
    G_flag_support := hGflag
    T_flag_support := hTflag
    surface_s_weight := hFs
    surface_ys_weight := hFys
    surface_total_weight := hFtotal
    x_injective := hinj
    degree_le := fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
    solution := fun gamma hgamma ↦ hsolution gamma (hsub hgamma)
    regular := fun gamma hgamma ↦ hregular gamma (hsub hgamma)
    on_prime := fun gamma hgamma ↦ componentSeeds_on_prime Omega G T
      (regularitySurface phi F) Gamma (selectedPoint phi selected) C gamma hgamma
    no_large_pencil := noLargeSelectedPencil_mono selected Gamma GammaC d e
      hsub hnoPencil
    characteristic_bound := hchar
  }

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily
