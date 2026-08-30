import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredThirdResidualFullBoxAdapter6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactPrimeSeedIncidence
open ContactFactorCaps ContactIdentityResidualGlobalFlagResearch
open ContactNestedFiveCapCoefficientBox6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredThirdResidual6750Research
open ContactAnchoredThirdResidualAdapter6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

theorem residualCountProvider_of_third_residual_full_old_core
    {D0 w0 Lmax s0 : Nat}
    (V : Submodule K
      (ContactFlagInterpolation6641Research.CoefficientIndex
        D0 w0 Lmax s0 → K))
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      D0 w0 Lmax s0 → K)
    (H Q T : Poly4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (sourceTotal sourceYS sourceS : Nat)
    (t y r : Nat) (hthi : t ≤ 1666) (hyhi : y ≤ 65) (hrhi : r ≤ 14)
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
      agreements ≤ ((Finset.univ : Finset I).filter (fun i ↦
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
    third_validity_of_full_old_core_bounds hthi hyhi hrhi
  have hcount := third_residual_count_lt t y r valid Q T hQ hrel
    hQbox hTcaps selected (commonCoreNonzeroSeeds H selected Gamma)
    u0 u1 hQsolution hTsolution hdegree hagreement hnoPencil
  omega

end

end ContactAnchoredThirdResidualFullBoxAdapter6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualFullBoxAdapter6750Research.residualCountProvider_of_third_residual_full_old_core
