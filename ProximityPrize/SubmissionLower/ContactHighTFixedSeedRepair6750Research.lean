import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedOldCoreLowQuotients6750Research
import ProximityPrize.SubmissionLower.ContactFirstSurvivingOriginalRQuotient6750Research
import ProximityPrize.SubmissionLower.ContactHighTFirstSurvivalRepairArithmetic6750Research
import ProximityPrize.SubmissionLower.ContactIteratedFlagKernelDerivativeVanish6750Research

 













namespace ProximityPrize.SubmissionLower
namespace ContactHighTFixedSeedRepair6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactIdentityResidualGlobalFlagResearch
open ContactFactorCaps
open ContactStackedSeedPartition6670Research
open ContactTwoTailParameters6750Research
open ContactKernelCommonGCD6750Research.E80260
open ContactNestedFiveCapCoefficientBox6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactKernelCommonDivisorQuotientRank6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactFirstSurvivingOriginalRQuotient6750Research
open ContactHighTDerivativeRouter6750Research
open ContactHighTFirstSurvivalRepairArithmetic6750Research
open ContactIteratedFlagKernelDerivativeVanish6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

 
def terminalDerivativeSeeds
    (G : GlobalPoly) (selected : K → Polynomial K)
    (Delta : Finset K) (j : Nat) : Finset K :=
  Delta.filter (fun gamma ↦
    specialization K (selected gamma) gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[j] G) = 0)

 
def fixedQuotientEquationSeeds
    (Q : GlobalPoly) (selected : K → Polynomial K)
    (Delta : Finset K) : Finset K :=
  Delta.filter (fun gamma ↦ specialization K (selected gamma) gamma Q = 0)

 


def FixedLowQuotientEquationCountProvider
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Delta : Finset K) (j : Nat) : Prop :=
  ∀ (z : BKernel u0 u1), z ≠ 0 →
    oldCoreQuotientLinear S z ≠ 0 →
    oldCoreQuotientLinear S z ∈
      nestedFiveCapCoefficientBox K
        (derivativeParentCutoff j -
          MvPolynomial.weightedTotalDegree (contactWeights 131071)
            (oldCommonCore S))
        131071 (1700 - oldCoreTotal S) (130 - oldCoreYS S)
          (29 - oldCoreS S) →
    (fixedQuotientEquationSeeds
      (oldCoreQuotientLinear S z) selected Delta).card ≤
        smallProfileBEquationCap

 


theorem fixed_low_quotient_product_derivatives_vanish
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (j : Nat) (hj : j ≤ 14) (z : BKernel u0 u1) (hz : z ≠ 0)
    (hQlow : oldCoreQuotientLinear S z ∈
      nestedFiveCapCoefficientBox K
        (derivativeParentCutoff j -
          MvPolynomial.weightedTotalDegree (contactWeights 131071)
            (oldCommonCore S))
        131071 (1700 - oldCoreTotal S) (130 - oldCoreYS S)
          (29 - oldCoreS S)) :
    ∀ gamma ∈ fixedSeeds selected Gamma S.QA S.QB S.QC,
      ∀ k ≤ j,
        specialization K (selected gamma) gamma
          ((MvPolynomial.pderiv (2 : Fin 4))^[k]
            (oldCommonCore S * oldCoreQuotientLinear S z)) = 0 := by
  intro gamma hgamma k hkj
  have hgammaGamma : gamma ∈ Gamma :=
    fixedSeeds_subset selected Gamma S.QA S.QB S.QC hgamma
  let support := (Finset.univ : Finset I).filter (fun i ↦
    (selected gamma).eval (IRSProfile.domain i) =
      u0 i + gamma * u1 i)
  have hsupport : 181874 ≤ support.card := by
    have h := hagreement gamma hgammaGamma
    simpa [support, agreements, n, errors] using h
  have hlow := reconstruct_mem_derivative_box_of_fixed_low_quotient
    S j hj z hz hQlow k hkj
  have hweight : k * (131071 - 1) < derivativeParentCutoff k := by
    unfold derivativeParentCutoff
    omega
  have hcapacity : derivativeParentCutoff k ≤
      (94 - k) * support.card + k * (131071 - 1) := by
    have hmul := Nat.mul_le_mul_left (94 - k) hsupport
    change (94 - k) * 181874 + k * 131070 ≤
      (94 - k) * support.card + k * 131070
    exact Nat.add_le_add_right hmul (k * 131070)
  have hvalues : ∀ i ∈ support,
      (selected gamma).eval (IRSProfile.domain i) =
        u0 i + gamma * u1 i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hv :=
    specialization_iterate_pderiv_R_eq_zero_of_high_kernel_and_low_box
      17096156 (derivativeParentCutoff k) 131071 1700 29 94 k
      IRSProfile.domain u0 u1 z.1 z.2 hlow
      (selected gamma) gamma support hweight
      (by simpa [w] using hdegree gamma hgammaGamma)
      hcapacity hvalues
  have hfactor : oldCommonCore S * oldCoreQuotientLinear S z =
      reconstruct K 17096156 131071 1700 29 z.1 :=
    mul_commonDivisorQuotientLinear
      17096156 131071 1700 29 94 IRSProfile.domain u0 u1
        (oldCommonCore S) (oldCommonCore_ne_zero S) S.oldCore_dvd_B z
  rw [hfactor]
  exact hv

 



theorem fixedSeeds_card_le_of_gap
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (j : Nat) (hj : j ≤ 14)
    (hgap : j * 50804 * nestedFiveCapChannelCount
        (1700 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S) <
      74974990)
    (hterminal :
      (terminalDerivativeSeeds (oldCommonCore S) selected
        (fixedSeeds selected Gamma S.QA S.QB S.QC) j).card ≤
          iteratedDerivativeReplacementCost j
            (oldCoreTotal S) (oldCoreYS S) (oldCoreS S))
    (hquotient : FixedLowQuotientEquationCountProvider S selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) j) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      iteratedDerivativeReplacementCost j
          (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        smallProfileBEquationCap := by
  let t := oldCoreTotal S
  let y := oldCoreYS S
  let r := oldCoreS S
  let Delta := fixedSeeds selected Gamma S.QA S.QB S.QC
  obtain ⟨z, hz, hQ, hfactor, hQlow⟩ :=
    exists_fixed_low_quotient S j hj hgap
  have hproducts := fixed_low_quotient_product_derivatives_vanish
    S selected Gamma hdegree hagreement j hj z hz hQlow
  let terminal := terminalDerivativeSeeds (oldCommonCore S) selected Delta j
  let quotient := fixedQuotientEquationSeeds
    (oldCoreQuotientLinear S z) selected Delta
  have hsubset : Delta ⊆ terminal ∪ quotient := by
    intro gamma hgamma
    have hor := terminal_R_or_quotient_specializes_zero
      (oldCommonCore S) (oldCoreQuotientLinear S z)
      (selected gamma) gamma j (hproducts gamma hgamma)
    rcases hor with hterm | hquot
    · exact Finset.mem_union_left quotient
        (Finset.mem_filter.mpr ⟨hgamma, hterm⟩)
    · exact Finset.mem_union_right terminal
        (Finset.mem_filter.mpr ⟨hgamma, hquot⟩)
  have hterminal' : terminal.card ≤
      iteratedDerivativeReplacementCost j t y r := by
    simpa only [terminal, Delta, t, y, r] using hterminal
  have hquotient' : quotient.card ≤ smallProfileBEquationCap := by
    apply hquotient z hz hQ
    simpa only [t, y, r] using hQlow
  calc
    Delta.card ≤ (terminal ∪ quotient).card := Finset.card_le_card hsubset
    _ ≤ terminal.card + quotient.card := Finset.card_union_le _ _
    _ ≤ iteratedDerivativeReplacementCost j t y r +
          smallProfileBEquationCap := Nat.add_le_add hterminal' hquotient'

 


theorem fixedSeeds_card_le_of_highT_route
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (j : Nat) (_hhigh : 1693 ≤ oldCoreTotal S)
    (hroute : HighTDerivativeRoute
      (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) j)
    (hterminal :
      (terminalDerivativeSeeds (oldCommonCore S) selected
        (fixedSeeds selected Gamma S.QA S.QB S.QC) j).card ≤
          iteratedDerivativeReplacementCost j
            (oldCoreTotal S) (oldCoreYS S) (oldCoreS S))
    (hquotient : FixedLowQuotientEquationCountProvider S selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) j) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      iteratedDerivativeReplacementCost j
          (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        smallProfileBEquationCap := by
  let t := oldCoreTotal S
  let y := oldCoreYS S
  let r := oldCoreS S
  have htHigh : 1693 ≤ t := by simpa only [t] using _hhigh
  have hy : y ≤ 65 := oldCommonCore_ys_le S
  have hr : r ≤ 14 := oldCommonCore_slope_le S
  have hj : j ≤ 14 := hroute.1.trans hr
  have hgap : j * 50804 * nestedFiveCapChannelCount
      (1700 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S) <
        74974990 := by
    by_cases hjzero : j = 0
    · subst j
      norm_num
    · have hresidual : derivativeFailureResidual
          (1700 - t) (130 - y) (29 - r) j < 74974990 := by
        rcases hroute.2.1 with hzero | hpositive
        · exact False.elim (hjzero hzero)
        · simpa [t, y, r, profileB, profileBNullity] using hpositive.2
      have hcodim : firstSurvivalLowSliceCodim
          (1700 - t) (130 - y) (29 - r) j ≤
            derivativeFailureResidual (1700 - t) (130 - y) (29 - r) j := by
        apply firstSurvivalLowSliceCodim_le_derivativeFailureResidual
        · dsimp only [t]
          omega
        · dsimp only [t, y]
          omega
        · dsimp only [t, r]
          omega
        · exact hj
      change firstSurvivalLowSliceCodim
        (1700 - t) (130 - y) (29 - r) j < 74974990
      exact hcodim.trans_lt hresidual
  exact fixedSeeds_card_le_of_gap S selected Gamma hdegree hagreement
    j hj hgap hterminal hquotient

 

theorem fixedSeeds_card_le_of_positive_highT_route
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (j : Nat) (_hjpos : 0 < j)
    (hhigh : 1693 ≤ oldCoreTotal S)
    (hroute : HighTDerivativeRoute
      (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) j)
    (hterminal :
      (terminalDerivativeSeeds (oldCommonCore S) selected
        (fixedSeeds selected Gamma S.QA S.QB S.QC) j).card ≤
          iteratedDerivativeReplacementCost j
            (oldCoreTotal S) (oldCoreYS S) (oldCoreS S))
    (hquotient : FixedLowQuotientEquationCountProvider S selected
      (fixedSeeds selected Gamma S.QA S.QB S.QC) j) :
    (fixedSeeds selected Gamma S.QA S.QB S.QC).card ≤
      iteratedDerivativeReplacementCost j
          (oldCoreTotal S) (oldCoreYS S) (oldCoreS S) +
        smallProfileBEquationCap :=
  fixedSeeds_card_le_of_highT_route S selected Gamma hdegree hagreement
    j hhigh hroute hterminal hquotient

end

end ContactHighTFixedSeedRepair6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactHighTFixedSeedRepair6750Research.fixed_low_quotient_product_derivatives_vanish
#print axioms ProximityPrize.SubmissionLower.ContactHighTFixedSeedRepair6750Research.fixedSeeds_card_le_of_highT_route
#print axioms ProximityPrize.SubmissionLower.ContactHighTFixedSeedRepair6750Research.fixedSeeds_card_le_of_positive_highT_route
