import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyAll6600Research

/-!
# Support-generic Z/YZ component aggregation

This is the support-indexed form of the accepted 66.42 tail replacement.
The inner recursive incidence is unchanged; only the positive large-pencil
charge and its global sum use `zCost + yzCost` instead of
`zCost + allCost`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZSupportResearch

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
open ContactIdentityResidualComponentFamily6600Research
open ContactResidualSupportParametersResearch

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Full regular-component aggregation with the accepted joint Z/YZ
large-pencil charge, for an arbitrary preserved residual support. -/
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz_of_direction
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (support : ResidualSupportParameters) (direction : FlagDegree)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ support.s)
    (hFys : wt residualYSWeights F ≤ support.ys)
    (hFtotal : wt residualTotalWeights F ≤ support.total)
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
    (hcost : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      ∀ t : ℕ, B.weightedCost (support.residualAgreementFlag t) C =
        t * B.weightedCost direction C + B.weightedCost unitYZFlag C)
    (hzyzPositive : ∀ C : RegularComponent Omega G T
      (regularitySurface phi F), 1 ≤ B.zCost C + B.yzCost C)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * flagMixed surfaceFlag cutFlag direction +
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
    fun C ↦ B.weightedCost direction C
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
    let S := regularComponentCurveStageOfSupport support F G T selected Gamma
      nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
      hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    apply recursive_curve_stratified_incidence_of_prime_flag_budget
      hphi S (fun r ↦ B.weightedCost r C) (B.primeBudget C)
      (degreeCost C) (unitCost C) U V (largeCost C)
    · intro t
      simpa only [degreeCost, unitCost] using hcost C t
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
    · simpa only [S, regularComponentCurveStageOfSupport] using hdegree
    · simpa only [S, regularComponentCurveStageOfSupport] using hunit
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
    (flagMixed surfaceFlag cutFlag direction)
    (flagMixed surfaceFlag cutFlag unitYZFlag)
    (flagMixed surfaceFlag cutFlag unitZFlag +
      flagMixed surfaceFlag cutFlag unitYZFlag)
    degreeCost unitCost largeCost hcomponent
    (by simpa only [degreeCost] using
      B.sum_weightedCost_le direction)
    (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
    hlargeSum

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualComponentFamilyYZSupportResearch
