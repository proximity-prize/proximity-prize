import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredFixedBranchAssembly6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredThirdResidualAdapter6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactFactorCaps ContactIdentityResidualGlobalFlagResearch
open ContactNestedFiveCapCoefficientBox6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredThirdResidual6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

 



theorem fiveCap_mem_globalCoefficientBox_of_caps
    {F : Type*} [Field F]
    {P : MvPolynomial (Fin 4) F}
    {D w T YS S D' L' S' : Nat}
    (hD : D ≤ D') (hT : T ≤ L') (hS : S ≤ S')
    (hbox : P ∈ nestedFiveCapCoefficientBox F D w T YS S) :
    P ∈ globalCoefficientBox F D' w L' S' := by
  change ∀ d ∈ P.support,
    d 1 + d 2 + d 3 ≤ T ∧ d 1 + d 2 ≤ YS ∧ d 2 ≤ S ∧
      d 0 + w * d 1 + (w - 1) * d 2 < D at hbox
  change ∀ d ∈ P.support,
    d 1 + d 3 ≤ L' ∧ d 2 ≤ S' ∧
      d 0 + w * d 1 + (w - 1) * d 2 < D'
  intro d hd
  have h := hbox d hd
  exact ⟨by omega, by omega, by omega⟩

 

theorem fiveCap_mem_thirdPivot_box
    {Q : Poly4} {t r D T YS S : Nat}
    (hD : D ≤ 47 * agreements)
    (hT : T ≤ 1667 - t) (hS : S ≤ 15 - r)
    (hbox : Q ∈ nestedFiveCapCoefficientBox K D w T YS S) :
    Q ∈ globalCoefficientBox K
      (thirdPivot t r).D (thirdPivot t r).w
      (thirdPivot t r).L (thirdPivot t r).s := by
  simpa only [thirdPivot, n, w, agreements] using
    (fiveCap_mem_globalCoefficientBox_of_caps
      (P := Q) hD hT hS hbox)

 



theorem fiveCap_mem_thirdStage_right_caps
    {Tpoly : Poly4} {t y r D T YS S : Nat}
    (hD : D ≤ 61 * agreements - (w * (y - 1) - r))
    (hT : T ≤ 4187 - t) (hS : S ≤ 19 - r)
    (hbox : Tpoly ∈ nestedFiveCapCoefficientBox K D w T YS S) :
    Tpoly.degreeOf 1 ≤ (thirdStage t y r).rightY ∧
      Tpoly.degreeOf 2 ≤ (thirdStage t y r).rightR ∧
      Tpoly.degreeOf 3 ≤ (thirdStage t y r).rightZ := by
  have hglobal : Tpoly ∈ globalCoefficientBox K
      (61 * agreements - (w * (y - 1) - r)) w
      (4187 - t) (19 - r) :=
    fiveCap_mem_globalCoefficientBox_of_caps hD hT hS hbox
  have hdegrees := degree_bounds_of_mem_box Tpoly
    (61 * agreements - (w * (y - 1) - r)) w
    (4187 - t) (19 - r) (by norm_num [w]) hglobal
  simpa only [thirdStage] using hdegrees

 

 







theorem residualCountProvider_of_third_residual
    {D0 w0 Lmax s0 : Nat}
    (V : Submodule K
      (ContactFlagInterpolation6641Research.CoefficientIndex
        D0 w0 Lmax s0 → K))
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      D0 w0 Lmax s0 → K)
    (H Q T : Poly4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (sourceTotal sourceYS sourceS : Nat)
    (t y r : Nat)
    (htlo : 897 ≤ t) (hthi : t ≤ 1659)
    (hylo : 38 ≤ y) (hyhi : y ≤ 65)
    (hrlo : 8 ≤ r) (hrhi : r ≤ 14)
    (vT : V)
    (hQ : Q ≠ 0) (hrel : IsRelPrime Q T)
    (hQfactor : ContactFlagInterpolation6641Research.reconstruct
      K D0 w0 Lmax s0 g = H * Q)
    (hTfactor : ContactFlagInterpolation6641Research.reconstruct
      K D0 w0 Lmax s0 vT.1 = H * T)
    {DQ TQ YSQ SQ DT TT YST ST : Nat}
    (hQfive : Q ∈ nestedFiveCapCoefficientBox K DQ w TQ YSQ SQ)
    (hQD : DQ ≤ 47 * agreements)
    (hQT : TQ ≤ 1667 - t) (hQS : SQ ≤ 15 - r)
    (hTfive : T ∈ nestedFiveCapCoefficientBox K DT w TT YST ST)
    (hTD : DT ≤ 61 * agreements - (w * (y - 1) - r))
    (hTT : TT ≤ 4187 - t) (hTS : ST ≤ 19 - r)
    (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      agreements ≤ ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (commonCoreNonzeroSeeds H selected Gamma) w errors) :
    ResidualCountProvider V g H selected Gamma
      sourceTotal sourceYS sourceS
      ((thirdStage t y r).regularCountCap + (thirdPivot t r).countCap) := by
  intro _hsourceNe _hsourceBox hgV hcancel
  have hQbox : Q ∈ globalCoefficientBox K
      (thirdPivot t r).D (thirdPivot t r).w
      (thirdPivot t r).L (thirdPivot t r).s :=
    fiveCap_mem_thirdPivot_box hQD hQT hQS hQfive
  have hTcaps :
      T.degreeOf 1 ≤ (thirdStage t y r).rightY ∧
      T.degreeOf 2 ≤ (thirdStage t y r).rightR ∧
      T.degreeOf 3 ≤ (thirdStage t y r).rightZ :=
    fiveCap_mem_thirdStage_right_caps hTD hTT hTS hTfive
  have hQsolution : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      specialization K (selected gamma) gamma Q = 0 := by
    intro gamma hgamma
    exact hcancel gamma hgamma ⟨g, hgV⟩ Q hQfactor
  have hTsolution : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      specialization K (selected gamma) gamma T = 0 := by
    intro gamma hgamma
    exact hcancel gamma hgamma vT T hTfactor
  have valid : ResidualValidity (thirdStage t y r) (thirdPivot t r) :=
    third_validity_of_hostile_bounds htlo hthi hylo hyhi hrlo hrhi
  have hcount := third_residual_count_lt t y r valid Q T hQ hrel
    hQbox hTcaps selected (commonCoreNonzeroSeeds H selected Gamma)
    u0 u1 hQsolution hTsolution hdegree hagreement hnoPencil
  omega

end

end ContactAnchoredThirdResidualAdapter6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research.fiveCap_mem_thirdPivot_box
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research.fiveCap_mem_thirdStage_right_caps
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research.residualCountProvider_of_third_residual
