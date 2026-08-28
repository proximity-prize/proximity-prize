import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZ6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamily6630Research
import ProximityPrize.SubmissionLower.ContactConstantSeedCoordinateResearch

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
open ContactConstantSeedCoordinateResearch
open ActualCurveCoordinateField
open ContactCongruentCuts6643Research

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
    (hTflag : PolynomialInFlagMod (Ideal.span {G}) cutFlag T)
    (hFs : wt residualSWeights F ≤ 10)
    (hFys : wt residualYSWeights F ≤ 48)
    (hFtotal : wt residualTotalWeights F ≤ 825)
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
  let Tred := hTflag.choose
  have hTredFlag : PolynomialInFlag cutFlag Tred := hTflag.choose_spec.1
  have hcongr : T - Tred ∈ C.1 := by
    have hspan : Ideal.span {G} ≤ C.1 := by
      apply Ideal.span_le.mpr
      intro A hA
      change A ∈ C.1
      rw [Set.mem_singleton_iff.mp hA]
      exact regularComponent_G_mem Omega G T (regularitySurface phi F) C
    exact hspan hTflag.choose_spec.2
  exact {
    nodes := nodes
    u0 := u0
    u1 := u1
    selected := selected
    F := F
    G := G
    T := Tred
    primeData := {
      ideal := C.1
      isPrime := inferInstance
      G_mem := regularComponent_G_mem Omega G T (regularitySurface phi F) C
      T_mem := (mem_iff_of_sub_mem C.1 hcongr).mp
        (regularComponent_T_mem Omega G T (regularitySurface phi F) C)
      H_not_mem := regularComponent_H_not_mem Omega G T
        (regularitySurface phi F) C
      ne_point := regularComponent_ne_point Omega G T
        (regularitySurface phi F) C
    }
    G_dvd_surface := hdiv
    G_flag_support := hGflag
    T_flag_support := hTredFlag
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
    (hTflag : PolynomialInFlagMod (Ideal.span {G}) cutFlag T)
    (hFs : wt residualSWeights F ≤ 10)
    (hFys : wt residualYSWeights F ≤ 48)
    (hFtotal : wt residualTotalWeights F ≤ 825)
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
    (hzPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F),
      Transcendental Omega (coordinate Omega C.1 2) → 1 ≤ B.zCost C)
    (hyzPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F),
      ¬ Transcendental Omega (coordinate Omega C.1 2) → 1 ≤ B.yzCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag cutFlag agreementDirection6630 +
        V * flagMixed surfaceFlag cutFlag unitYZFlag +
        (a - d) * ((e + 1) * flagMixed surfaceFlag cutFlag unitZFlag +
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
    fun C ↦ (e + 1) * B.zCost C + B.yzCost C
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (a - d) * largeCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStage6630 F G T selected Gamma nodes x u0 u1
      p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
      hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    change GammaC.card * (a - d) ≤
      U * degreeCost C + V * unitCost C + (a - d) * largeCost C
    by_cases hZ : Transcendental Omega (coordinate Omega C.1 2)
    · have hrec := recursive_curve_stratified_incidence_of_prime_flag_budget
        hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
        (degreeCost C) (unitCost C) U V (B.zCost C)
        (fun t => by
          simpa only [degreeCost, unitCost] using
            ContactPrimeFlagBudgetFamily6630Research.PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag6630
              B C t)
        hda
        (fun gamma hgamma => hagreement gamma (hsub hgamma))
        (fun D hmany => by
          have hcard : GammaC.card ≤ e + 1 :=
            D.stage.card_le_pencil_of_many_identities hmany
          have hscaled : GammaC.card * (a - d) ≤ (e + 1) * (a - d) :=
            Nat.mul_le_mul_right (a - d) hcard
          have hmul := Nat.mul_le_mul_left ((e + 1) * (a - d))
            (hzPositive C hZ)
          exact hscaled.trans (by simpa only [Nat.mul_one] using hmul))
        (by simpa only [S, regularComponentCurveStage6630] using hdegree)
        (by simpa only [S, regularComponentCurveStage6630] using hunit)
      calc
        GammaC.card * (a - d) ≤
            U * degreeCost C + V * unitCost C +
              (e + 1) * (a - d) * B.zCost C := hrec
        _ ≤ (U * degreeCost C + V * unitCost C +
              (e + 1) * (a - d) * B.zCost C) +
              (a - d) * B.yzCost C := Nat.le_add_right _ _
        _ = U * degreeCost C + V * unitCost C +
              (a - d) * largeCost C := by
          dsimp only [largeCost]
          ring
    · have hZalg : IsAlgebraic Omega (coordinate Omega C.1 2) := not_not.mp hZ
      have hcard : GammaC.card ≤ 1 :=
        selected_seed_set_card_le_one_of_seedCoordinate_isAlgebraic
          phi C.1 selected GammaC (fun gamma hgamma => S.on_prime gamma hgamma) hZalg
      have hscaled : GammaC.card * (a - d) ≤ a - d := by
        simpa only [one_mul] using Nat.mul_le_mul_right (a - d) hcard
      have hyz := hyzPositive C hZ
      have hcharged : a - d ≤ (a - d) * B.yzCost C := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a - d) hyz
      have htail : (a - d) * B.yzCost C ≤ (a - d) * largeCost C := by
        apply Nat.mul_le_mul_left
        dsimp only [largeCost]
        omega
      exact hscaled.trans (hcharged.trans (htail.trans (Nat.le_add_left _ _)))
  have hlargeSum :
      (∑ C : RegularComponent Omega G T H, largeCost C) ≤
        (e + 1) * flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitYZFlag := by
    calc
      (∑ C : RegularComponent Omega G T H, largeCost C) =
          (e + 1) * (∑ C : RegularComponent Omega G T H, B.zCost C) +
            ∑ C : RegularComponent Omega G T H, B.yzCost C := by
        simp only [largeCost, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (e + 1) * flagMixed surfaceFlag cutFlag unitZFlag +
          flagMixed surfaceFlag cutFlag unitYZFlag :=
        Nat.add_le_add (Nat.mul_le_mul_left (e + 1) B.sum_zCost_le)
          B.sum_yzCost_le
  simpa only [one_mul] using aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a - d) U V 1
    (flagMixed surfaceFlag cutFlag agreementDirection6630)
    (flagMixed surfaceFlag cutFlag unitYZFlag)
    ((e + 1) * flagMixed surfaceFlag cutFlag unitZFlag +
      flagMixed surfaceFlag cutFlag unitYZFlag)
    degreeCost unitCost largeCost (by simpa only [one_mul] using hcomponent)
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le agreementDirection6630)
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    hlargeSum

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZCaps6630Research
