import ProximityPrize.SubmissionLower.ContactStackedSeedPartition
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport
import ProximityPrize.SubmissionLower.ContactAsymmetricResidualStage
import ProximityPrize.SubmissionLower.ContactSingularBranchParameterized

namespace ProximityPrize.SubmissionLower.ContactStackedResidualCells

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCD
open ContactStackedParameters
open ContactStackedGCDCover
open ContactStackedSeedPartition
open ContactStackedBoxTransport
open ContactRecursiveResidualStages
open ContactTightSingularLedger
open ContactSingularLedger
open ContactSingularBranch
open ContactSingularBranchParameterized
open ContactAsymmetricResidualStage

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 35000

abbrev StackedPoly := MvPolynomial (Fin 4) IRSProfile.Field
local instance : GCDMonoid StackedPoly :=
  UniqueFactorizationMonoid.toGCDMonoid StackedPoly

variable {K Iota : Type} [Field K]
local instance : DecidableEq Iota := Classical.decEq Iota

theorem asymmetric_stage_count_lt_of_regular_factors
    (P : UnequalParameters)
    (S : ContactTightSingularLedger.TightParameters)
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p]
    (hs : 1 ≤ S.s) (hsmall : S.s < p) (hw : 1 ≤ S.w)
    (hchar : S.w < p) (hDw : S.w < S.kappa * S.D)
    (hj : 1 ≤ S.algebraicCap)
    (hjYSmall : S.implicitYCap < p)
    (hjZSmall : S.algebraicCap < p)
    (hmixedSmall : 2 * S.implicitYCap * S.algebraicCap < p)
    (hwa : S.w < S.a) (han : S.a ≤ S.n)
    (hbox : Q ∈ globalCoefficientBox K S.D S.w S.L S.s)
    (hgap : 0 < P.gap) (_hgapEq : S.gap = P.gap)
    (hY : (S.D - 1) / S.w ≤ P.leftY)
    (hR : S.s ≤ P.leftR) (hZ : S.L ≤ P.leftZ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = S.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ S.w)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      S.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma S.w S.errors)
    (hregular : ∀ F : ContactAsymmetricResidualStage.RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card * P.gap ≤
        (P.n - P.w) * dot P.agreement (regularVector P F.1) +
          (P.errors + 1) * P.gap * (regularVector P F.1).z) :
    Gamma.card < P.regularCountCap + S.countCap + 1 := by
  classical
  have hcover := card_le_regular_sum_add_singular Q T hQ
    S.D S.w S.L S.s p hs hsmall hw hDw hj hjZSmall hbox
    selected Gamma hQsolution hTsolution
  have hregularScaled := sum_regular_counts_bound P Q T selected Gamma
    (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
    hregular
  have hregularCap :
      (∑ F : ContactAsymmetricResidualStage.RegularIndex Q,
        (regularPairSeeds Q T selected Gamma F).card) ≤ P.regularCountCap :=
    P.regular_count_le _ hgap hregularScaled
  have hsingularOld :=
    ContactSingularBranchParameterized.TightParameters.singularSeeds_count_le_countCap
      S Q hQ hbox hs hsmall hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
      hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil
  have hsingular :
      (ContactAsymmetricResidualStage.singularSeeds Q selected Gamma).card ≤
        S.countCap := by
    change (ContactSingularBranch.singularSeeds Q selected Gamma).card ≤
      S.countCap
    exact hsingularOld
  omega

theorem quotientB_ne_zero
    (QA QB : StackedPoly) (hQB : QB ≠ 0) : quotientB QA QB ≠ 0 := by
  intro hz
  apply hQB
  rw [b_eq_gcd12_mul_quotientB QA QB, hz, mul_zero]

theorem middleQuotient_ne_zero
    (QA QB QC : StackedPoly) (hQA : QA ≠ 0) :
    middleQuotient QA QB QC ≠ 0 := by
  intro hz
  apply gcd12_ne_zero (B := QB) hQA
  rw [gcd12_eq_gcd123_mul_middleQuotient QA QB QC, hz, mul_zero]

end

end ProximityPrize.SubmissionLower.ContactStackedResidualCells
