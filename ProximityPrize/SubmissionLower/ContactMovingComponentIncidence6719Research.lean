import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingStageZero6719Research
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch

namespace ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research
open scoped Classical BigOperators
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactFlagBezout6543Research
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactIdentityResidualGlobalFlagResearch ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualComponentFamily6600Research
open ContactStratifiedResidualComponentAdapter6600Research ContactWeakSeparableSeparatorResearch
open ContactMovingStageZero6719Research ContactMovingStageInvariant6719Research
open ContactMovingCurveBudget6719Research ContactIntrinsicRationalZero6719Research
noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 50000
variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

theorem proper_cut_seed_bound_of_moving_budgets
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (a0 b0 s0 : ℕ)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).s)
    (hFys : wt residualYSWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).ys)
    (hFtotal : wt residualTotalWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).total)
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
    (base : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      SeparableLiteralCoordinate C.1)
    (B : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      MovingPoleBudget C.1 (regularitySurface phi F) (surfaceMap phi (polyG K F)))
    (hzyzPositive : ∀ C : RegularComponent Omega G T (regularitySurface phi F),
      1 ≤ (B C).zCost + (B C).yzCost)
    (zSum yzSum allSum movingSum : ℕ)
    (hz : (∑ C, (B C).zCost) ≤ zSum)
    (hyz : (∑ C, (B C).yzCost) ≤ yzSum)
    (hall : (∑ C, (B C).allCost) ≤ allSum)
    (hmoving : (∑ C, (B C).movingCost) ≤ movingSum)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a-d) ≤
      U * ContactMovingStageZero6719Research.degreeCost a0 b0 s0 zSum yzSum allSum movingSum +
      V * ContactMovingStageZero6719Research.unitCost a0 b0 s0 zSum yzSum allSum +
      (e+1)*(a-d)*(zSum+yzSum) := by
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
    fun C ↦ ContactMovingStageZero6719Research.degreeCost a0 b0 s0
      (B C).zCost (B C).yzCost (B C).allCost (B C).movingCost
  let unitCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ ContactMovingStageZero6719Research.unitCost a0 b0 s0
      (B C).zCost (B C).yzCost (B C).allCost
  let largeCost : RegularComponent Omega G T H → ℕ :=
    fun C ↦ (B C).zCost + (B C).yzCost
  have hcomponent : ∀ C : RegularComponent Omega G T H,
      (componentSeeds Omega G T H Gamma
          (selectedPoint phi selected) C).card * (a - d) ≤
        U * degreeCost C + V * unitCost C +
          (e + 1) * (a - d) * largeCost C := by
    intro C
    let GammaC := componentSeeds Omega G T H Gamma
      (selectedPoint phi selected) C
    let S := regularComponentCurveStageOfSupport (ContactMovingAgreementCertificate6719Research.support a0 b0 s0) F G T selected Gamma
      nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
      hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
    have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
      (selectedPoint phi selected) C
    have hInv : StageInvariant (B C).zCost (B C).yzCost (B C).allCost (B C).movingCost S := by
      refine ⟨?_, B C, rfl, rfl, rfl, rfl⟩
      exact RationalZeroCriterion.of_separator C.1 (base C)
    apply recursive_curve_moving_bound hphi S
      (B C).zCost (B C).yzCost (B C).allCost (B C).movingCost hInv
      U V (largeCost C)
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
  have hdegreeSum : (∑ C : RegularComponent Omega G T H, degreeCost C) ≤
      ContactMovingStageZero6719Research.degreeCost a0 b0 s0 zSum yzSum allSum movingSum := by
    simp only [degreeCost, ContactMovingStageZero6719Research.degreeCost,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a0 hz)
        (Nat.mul_le_mul_left b0 hyz)) (Nat.mul_le_mul_left s0 hall)) hmoving
  have hunitSum : (∑ C : RegularComponent Omega G T H, unitCost C) ≤
      ContactMovingStageZero6719Research.unitCost a0 b0 s0 zSum yzSum allSum := by
    simp only [unitCost, ContactMovingStageZero6719Research.unitCost,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ hz) (Nat.mul_le_mul_left _ hyz))
      (Nat.mul_le_mul_left _ hall)
  have hlargeSum : (∑ C : RegularComponent Omega G T H, largeCost C) ≤ zSum+yzSum := by
    simpa only [largeCost, Finset.sum_add_distrib] using Nat.add_le_add hz hyz
  exact aggregate_component_stratified_incidence G T H Gamma
    (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
    (ContactMovingStageZero6719Research.degreeCost a0 b0 s0 zSum yzSum allSum movingSum)
    (ContactMovingStageZero6719Research.unitCost a0 b0 s0 zSum yzSum allSum)
    (zSum+yzSum) degreeCost unitCost largeCost hcomponent hdegreeSum hunitSum hlargeSum


/-- . -/
theorem regular_component_moving_incidence
    (hphi : Function.Injective phi)
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Omega)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (p e d a U V : ℕ) [CharP Omega p]
    (surfaceFlag cutFlag : FlagDegree)
    (a0 b0 s0 : ℕ)
    (hdiv : G ∣ surfaceMap phi F)
    (hGflag : PolynomialInFlag surfaceFlag G)
    (hTflag : PolynomialInFlag cutFlag T)
    (hFs : wt residualSWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).s)
    (hFys : wt residualYSWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).ys)
    (hFtotal : wt residualTotalWeights F ≤ (ContactMovingAgreementCertificate6719Research.support a0 b0 s0).total)
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
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma d e)
    (hchar : d < p) (hda : d < a)
    (C : RegularComponent Omega G T (regularitySurface phi F))
    (base : SeparableLiteralCoordinate C.1)
    (B : MovingPoleBudget C.1 (regularitySurface phi F) (surfaceMap phi (polyG K F)))
    (hzyzPositive : 1 ≤ B.zCost + B.yzCost)
    (hdegree : ∀ k ≤ d,
      (nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (nodes.card - k) * (a - d) ≤ V * (a - k)) :
    (componentSeeds Omega G T (regularitySurface phi F) Gamma
      (selectedPoint phi selected) C).card * (a-d) ≤
      U * ContactMovingStageZero6719Research.degreeCost a0 b0 s0
        B.zCost B.yzCost B.allCost B.movingCost +
      V * ContactMovingStageZero6719Research.unitCost a0 b0 s0 B.zCost B.yzCost B.allCost +
      (e+1)*(a-d)*(B.zCost+B.yzCost) := by
  classical
  let H := regularitySurface phi F
  let GammaC := componentSeeds Omega G T H Gamma
    (selectedPoint phi selected) C
  let S := regularComponentCurveStageOfSupport (ContactMovingAgreementCertificate6719Research.support a0 b0 s0) F G T selected Gamma
    nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
    hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
  have hsub : GammaC ⊆ Gamma := componentSeeds_subset Omega G T H Gamma
    (selectedPoint phi selected) C
  have hInv : StageInvariant B.zCost B.yzCost B.allCost B.movingCost S := by
    refine ⟨?_, B, rfl, rfl, rfl, rfl⟩
    exact RationalZeroCriterion.of_separator C.1 base
  apply recursive_curve_moving_bound hphi S
    B.zCost B.yzCost B.allCost B.movingCost hInv
    U V (B.zCost+B.yzCost)
  · exact hda
  · intro gamma hgamma
    exact hagreement gamma (hsub hgamma)
  · intro D hmany
    have hcard : GammaC.card ≤ e + 1 :=
      D.stage.card_le_pencil_of_many_identities hmany
    have hscaled : GammaC.card * (a - d) ≤ (e + 1) * (a - d) :=
      Nat.mul_le_mul_right (a - d) hcard
    have hcharged : (e + 1) * (a - d) ≤
        (e + 1) * (a - d) * (B.zCost+B.yzCost) := by
      have hmul := Nat.mul_le_mul_left ((e + 1) * (a - d))
        hzyzPositive
      simpa only [Nat.mul_one] using hmul
    exact hscaled.trans hcharged
  · simpa only [S, regularComponentCurveStageOfSupport] using hdegree
  · simpa only [S, regularComponentCurveStageOfSupport] using hunit

end
end ProximityPrize.SubmissionLower.ContactMovingComponentIncidence6719Research
