import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZ6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research

/-!
# YZ-safe recursive component aggregation

The degree-zero terminal branch needs only a positive charge, not the full
all-coordinate projection.  When the shared Z and YZ projection costs are
jointly positive, charge the branch to `zCost + yzCost`.  Their global sums
are already bounded by the unit-Z and unit-YZ mixed volumes.

This file is deliberately generic: the geometric producer proving joint
positivity is separate from this finite incidence and aggregation theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZCaps6630Research

open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactFlagBezout6543Research
open ContactIdentityResidualCurveIteration6630Research
open ContactIdentityResidualCurveTerminalIncidence6630Research
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualGlobalFlag6630Research
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactPrimeFlagBudgetFamily6630Research
open ContactStratifiedResidualComponentAdapter6600Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactNearPencil6630FlagResearch
open ContactIdentityResidualComponentFamily6600Research

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota


/-- Canonical initial inner-recursion stage at the exact 66.30 cumulative
surface caps. -/
def regularComponentCurveStage6630
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d : ℕ) [CharP Omega p] (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ 8)
    (hFys : wt residualYSWeights F ≤ 40)
    (hFtotal : wt residualTotalWeights F ≤ 617)
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
    CurveResidualStage6630 phi
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

/-- Full component aggregation with a joint Z/YZ fallback for the
degree-zero terminal branch.  The sole new premise is the weakest
consumer-shaped positivity statement: the sum of the two charges is at
least one on every retained regular component. -/
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ 8)
    (hFys : wt residualYSWeights F ≤ 40)
    (hFtotal : wt residualTotalWeights F ≤ 617)
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
    (hzyzPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F), 1 ≤ B.zCost C + B.yzCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag cutFlag agreementDirection6630 +
        V * flagMixed surfaceFlag cutFlag unitYZFlag +
        (e + 1) * (a - d) *
          (flagMixed surfaceFlag cutFlag unitZFlag +
            flagMixed surfaceFlag cutFlag unitYZFlag) := by
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
    fun C ↦ B.weightedCost agreementDirection6630 C
  let unitCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.weightedCost unitYZFlag C
  let largeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ B.zCost C + B.yzCost C
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (e + 1) * (a - d) * largeCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStage6630 F G T selected Gamma nodes x u0 u1
      p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
      hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    apply recursive_curve_stratified_incidence_of_prime_flag_budget
      hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
      (degreeCost C) (unitCost C) U V (largeCost C)
    · intro t
      simpa only [degreeCost, unitCost] using
        ContactPrimeFlagBudgetFamily6630Research.PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag6630
          B C t
    · exact hda
    · intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    · intro D hmany
      have hcard : GammaC.card ≤ e + 1 :=
        D.stage.card_le_pencil_of_many_identities hmany
      have hscaled : GammaC.card * (a - d) ≤ (e + 1) * (a - d) :=
        Nat.mul_le_mul_right (a - d) hcard
      have hcharged : (e + 1) * (a - d) ≤
          (e + 1) * (a - d) * largeCost C := by
        have hmul := Nat.mul_le_mul_left ((e + 1) * (a - d))
          (hzyzPositive C)
        simpa only [largeCost, Nat.mul_one] using hmul
      exact hscaled.trans hcharged
    · simpa only [S, regularComponentCurveStage6630] using hdegree
    · simpa only [S, regularComponentCurveStage6630] using hunit
  have hlargeSum :
      (∑ C : RegularComponent Omega G T H, largeCost C) ≤
        flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitYZFlag := by
    calc
      (∑ C : RegularComponent Omega G T H, largeCost C) =
          (∑ C : RegularComponent Omega G T H, B.zCost C) +
            ∑ C : RegularComponent Omega G T H, B.yzCost C := by
        simp only [largeCost, Finset.sum_add_distrib]
      _ ≤ flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitYZFlag :=
        Nat.add_le_add B.sum_zCost_le B.sum_yzCost_le
  exact aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a - d) U V (e + 1)
    (flagMixed surfaceFlag cutFlag agreementDirection6630)
    (flagMixed surfaceFlag cutFlag unitYZFlag)
    (flagMixed surfaceFlag cutFlag unitZFlag +
      flagMixed surfaceFlag cutFlag unitYZFlag)
    degreeCost unitCost largeCost hcomponent
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le agreementDirection6630)
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    hlargeSum

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZCaps6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZCaps6630Research.proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz
