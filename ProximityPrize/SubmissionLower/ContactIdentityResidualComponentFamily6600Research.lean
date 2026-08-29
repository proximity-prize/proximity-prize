import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch
import ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter6600Research

/-!
# Recursive score-66 incidence over a regular component family

This module is the exact join between the componentwise adaptive pole budget
and the actual-identity recursion on an arbitrary curve prime.  One shared
`PrimeFlagBudgetFamily` is assigned on the original regular components.  Its
prime budget is transported through each component's private residual path,
and only then are the three unit costs summed.

The large-pencil implication is kept explicit.  It is the narrow remaining
leaf saying that a terminal many-identity branch, whose current `Z`
coordinate is transcendental, has positive original `Z` pole cost.
-/

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

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- The canonical initial inner-recursion state attached to one regular
component of a proper outer cut. -/
def regularComponentCurveStage
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d : ℕ) [CharP Omega p] (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ 6)
    (hFys : wt residualYSWeights F ≤ 33)
    (hFtotal : wt residualTotalWeights F ≤ 582)
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
      x p e surfaceFlag cutFlag d := by
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

/-- Full regular-component aggregation after recursive identity removal.

The conclusion is the literal mixed-flag expression needed at one outer
proper cut.  `hlarge` is the sole branch-local premise not supplied by the
shared prime flag budget itself.
-/
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ 6)
    (hFys : wt residualYSWeights F ≤ 33)
    (hFtotal : wt residualTotalWeights F ≤ 582)
    (hinj : Set.InjOn x nodes)
    (hdegreeSelected : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ d)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
        (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
          (phi Polynomial.X))
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) G = 0)
    (hTpoint : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma d e)
    (hchar : d < p) (hda : d < a)
    (B : PrimeFlagBudgetFamily (G := G) (T := T)
      (H := regularitySurface phi F) surfaceFlag cutFlag)
    (hlarge : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      let GammaC := componentSeeds Omega G T (regularitySurface phi F) Gamma
        (selectedPoint phi selected) C
      let S := regularComponentCurveStage F G T selected Gamma nodes x u0 u1
        p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
        hdegreeSelected hsolution hregular hnoPencil hchar C
      ∀ D : S.TerminalDescendant,
        D.degree < D.stage.identities.card →
          GammaC.card * (a - d) ≤ (e + 1) * (a - d) * B.zCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag cutFlag agreementDirection6600 +
        V * flagMixed surfaceFlag cutFlag unitYZFlag +
        (e + 1) * (a - d) * flagMixed surfaceFlag cutFlag unitZFlag := by
  classical
  let H := regularitySurface phi F
  have hHp : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint phi selected gamma) H ≠ 0 := by
    intro gamma hgamma
    change MvPolynomial.eval (selectedPoint phi selected gamma)
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact hregular gamma hgamma
  let degreeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost agreementDirection6600 C
  let unitCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost unitYZFlag C
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (e + 1) * (a - d) * B.zCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStage F G T selected Gamma nodes x u0 u1
      p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
      hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    apply recursive_curve_stratified_incidence_of_prime_flag_budget
      hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
      (degreeCost C) (unitCost C) U V (B.zCost C)
    · intro t
      simpa only [degreeCost, unitCost] using
        B.weightedCost_residualAgreementFlag C t
    · exact hda
    · intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    · simpa only [GammaC, S, H] using hlarge C
    · simpa only [S, regularComponentCurveStage] using hdegree
    · simpa only [S, regularComponentCurveStage] using hunit
  exact aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a - d) U V (e + 1)
    (flagMixed surfaceFlag cutFlag agreementDirection6600)
    (flagMixed surfaceFlag cutFlag unitYZFlag)
    (flagMixed surfaceFlag cutFlag unitZFlag)
    degreeCost unitCost B.zCost hcomponent
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le agreementDirection6600)
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    B.sum_zCost_le

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamily6600Research
