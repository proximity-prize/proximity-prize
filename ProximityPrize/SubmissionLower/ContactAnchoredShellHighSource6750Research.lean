import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHighSourceAssembly6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredShellSelector6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighSourceAssembly6750Research

open scoped Classical BigOperators
open ContactTranslation
open ContactFlagInterpolation6641Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighKernelSelectorRealization6750Research
open ContactAnchoredHighSourceContactCap6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactResidualContactDegree6750Research
open ContactCommonCoreBranchPartition6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 250000

universe v

variable {K : Type} [Field K]
variable {I : Type v} [Fintype I]

local instance : DecidableEq K := Classical.decEq K

 
def shellCellFamilyIndex {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    HighFamilyIndex :=
  ⟨selectedTotal t y r,
    Nat.lt_succ_iff.mpr
      (FirstDerivativeShell.selectedTotal_le_4186 cell)⟩

@[simp] theorem highFamilyCap_shellCellFamilyIndex
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    highFamilyCap (shellCellFamilyIndex cell) = selectedTotal t y r :=
  rfl

theorem FirstDerivativeShell.exists_highSourceHull_selected_low_quotient
    {t y r c sourceT sourceYS sourceS : Nat}
    (cell : FirstDerivativeShell t y r)
    (nodes u0 u1 : I → K) (hcard : Fintype.card I = domainSize)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (hfixed : reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0)
    (hfixedBox : reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
      nestedFiveCapCoefficientBox K (48 * agreements) 131071
        sourceT sourceYS sourceS)
    (hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (canonicalHighSourceCore nodes u0 u1 g) = c)
    (hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights
      (canonicalHighSourceCore nodes u0 u1 g) = t)
    (hHys : MvPolynomial.weightedTotalDegree residualYSWeights
      (canonicalHighSourceCore nodes u0 u1 g) = y)
    (hHs : MvPolynomial.weightedTotalDegree residualSWeights
      (canonicalHighSourceCore nodes u0 u1 g) = r) :
    ∃ theta : LinearMap.ker
        (constraintMap K 11458062 131071 (selectedTotal t y r) 18 63
          nodes u0 u1),
      theta ≠ 0 ∧
      ∃ Q : Poly4 K, Q ≠ 0 ∧
        canonicalHighSourceCore nodes u0 u1 g * Q =
          reconstruct K 11458062 131071 (selectedTotal t y r) 18 theta.1 ∧
        Q ∈ nestedFiveCapCoefficientBox K
          (11407258 - c) 131071
          (selectedTotal t y r - t) (familyYSCap - y)
          (familySlopeCap - r) ∧
        reconstruct K 11458062 131071 (selectedTotal t y r) 18 theta.1 ∈
          nestedFiveCapCoefficientBox K 11407258 131071
            (selectedTotal t y r) familyYSCap familySlopeCap := by
  have hcUpper : c ≤ 48 * agreements - 1 := by
    rw [← hHcontact]
    exact canonicalHighSourceCore_contact_le_47agreements_sub_one
      nodes u0 u1 g hfixed hfixedBox
  have hdiv : ∀ theta : LinearMap.ker
      (constraintMap K 11458062 131071 (selectedTotal t y r) 18 63
        nodes u0 u1),
      canonicalHighSourceCore nodes u0 u1 g ∣
        reconstruct K 11458062 131071 (selectedTotal t y r) 18 theta.1 := by
    intro theta
    have h := canonicalHighSourceCore_dvd_fullKernel_reconstruct
      nodes u0 u1 g (shellCellFamilyIndex cell) theta
    simpa only [highFamilyCap_shellCellFamilyIndex] using h
  obtain ⟨theta, htheta, Q, hQ, hfactor, hQbox, _hQenvelope, hlow⟩ :=
    ContactAnchoredHighKernelSelectorRealization6750Research.FirstDerivativeShell.exists_selected_m61_low_quotient
      (K := K) cell nodes u0 u1 hcard
      (canonicalHighSourceCore nodes u0 u1 g)
      (canonicalHighSourceCore_ne_zero_of_fixed nodes u0 u1 g hfixed)
      hHcontact hcUpper hHtotal hHys hHs hdiv
  exact ⟨theta, htheta, Q, hQ, hfactor, hQbox, hlow⟩

theorem FirstDerivativeShell.commonCoreZeroSeeds_card_le_of_highSourceHull
    [DecidableEq I]
    {t y r c sourceT sourceYS sourceS : Nat}
    (cell : FirstDerivativeShell t y r)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (hcard : Fintype.card I = domainSize)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (hfixed : reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0)
    (hfixedBox : reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
      nestedFiveCapCoefficientBox K (48 * agreements) 131071
        sourceT sourceYS sourceS)
    (hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (canonicalHighSourceCore nodes u0 u1 g) = c)
    (hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights
      (canonicalHighSourceCore nodes u0 u1 g) = t)
    (hHys : MvPolynomial.weightedTotalDegree residualYSWeights
      (canonicalHighSourceCore nodes u0 u1 g) = y)
    (hHs : MvPolynomial.weightedTotalDegree residualSWeights
      (canonicalHighSourceCore nodes u0 u1 g) = r)
    (selected : K → Polynomial K) (Delta : Finset K)
    (semantics : FixedCandidateSemantics nodes u0 u1 selected Delta)
    (anchoredCap : Nat)
    (stageBound : ∀
      (theta : LinearMap.ker
      (constraintMap K 11458062 131071 (selectedTotal t y r) 18 63
          nodes u0 u1))
      (Q : Poly4 K),
      theta ≠ 0 → Q ≠ 0 →
      canonicalHighSourceCore nodes u0 u1 g * Q =
        reconstruct K 11458062 131071 (selectedTotal t y r) 18 theta.1 →
      Q ∈ nestedFiveCapCoefficientBox K
        (11407258 - c) 131071
        (selectedTotal t y r - t) (familyYSCap - y)
        (familySlopeCap - r) →
      ∃ C : AnchoredStageCertificate
          (canonicalHighSourceCore nodes u0 u1 g) Q selected
            (commonCoreZeroSeeds
              (canonicalHighSourceCore nodes u0 u1 g) selected Delta),
        C.cost ≤ anchoredCap) :
    (commonCoreZeroSeeds
      (canonicalHighSourceCore nodes u0 u1 g) selected Delta).card ≤
        anchoredCap := by
  let H := canonicalHighSourceCore nodes u0 u1 g
  obtain ⟨theta, htheta, Q, hQ, hfactor, hQbox, hlow⟩ :=
    FirstDerivativeShell.exists_highSourceHull_selected_low_quotient
      (K := K) cell nodes u0 u1 hcard g hfixed hfixedBox
        hHcontact hHtotal hHys hHs
  obtain ⟨stage, hstage⟩ := stageBound theta Q htheta hQ hfactor hQbox
  have hHzero : ∀ gamma ∈ commonCoreZeroSeeds H selected Delta,
      specialization K (selected gamma) gamma H = 0 := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hproductDerivative :
      ∀ gamma ∈ commonCoreZeroSeeds H selected Delta,
        specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4) (H * Q)) = 0 := by
    intro gamma hgamma
    have hgammaDelta : gamma ∈ Delta :=
      commonCoreZeroSeeds_subset H selected Delta hgamma
    rw [hfactor]
    exact specialization_pderiv_R_eq_zero_of_selected_m61_high_member
      (selectedTotal t y r) nodes u0 u1 theta.1 theta.2 hlow
      (selected gamma) gamma (semantics.support gamma)
      (semantics.selected_degree gamma hgammaDelta)
      (semantics.agreement_card gamma hgammaDelta)
      (semantics.agreement_values gamma hgammaDelta)
  exact (stage.card_le_cost
    (canonicalHighSourceCore_ne_zero_of_fixed nodes u0 u1 g hfixed) hQ hHzero
      hproductDerivative).trans hstage

end

end ContactAnchoredHighSourceAssembly6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceAssembly6750Research.FirstDerivativeShell.exists_highSourceHull_selected_low_quotient
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceAssembly6750Research.FirstDerivativeShell.commonCoreZeroSeeds_card_le_of_highSourceHull
