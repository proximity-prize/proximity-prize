import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
import ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research
import ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

/-!
# Selected-family composition for the stacked 67.40 route
-/

namespace ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactStackedParameters6670Research
open ContactStackedInterpolation6670Research
open ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactStackedResidualCells6670Research
open ContactStackedPromotedArithmetic6670Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

theorem selectedNoLargePencilBound_of_fixedCellCountProvider6670
    (hfixed : ∀ (A B C : GlobalPoly) (gamma : IRSProfile.Field),
      A ≠ 0 → B ≠ 0 → C ≠ 0 →
      A ∈ globalCoefficientBox IRSProfile.Field (45 * agreements) w 20000 14 →
      B ∈ globalCoefficientBox IRSProfile.Field (76 * agreements) w 1450 23 →
      C ∈ globalCoefficientBox IRSProfile.Field (45 * agreements) w 50000 14 →
      (fixedCell IRSProfile.Field gamma A B C).card < fixedCost) :
    SelectedNoLargePencilBound
      IRSProfile.domain 131071 80162 274980727111395087 := by
  intro u0 u1
  rcases exists_stacked_interpolants_with_recursive_cover u0 u1 with
    ⟨QA, QB, QC, hQA_ne, hboxA, hQB_ne, hboxB, hQC_ne, hboxC, hflagB, huniv⟩
  have hfixed_bound : ∀ gamma : IRSProfile.Field,
      (fixedCell IRSProfile.Field gamma QA QB QC).card < fixedCost := by
    intro gamma
    exact hfixed QA QB QC gamma hQA_ne hQB_ne hQC_ne hboxA hboxB hboxC
  have hres1_bound : ∀ gamma : IRSProfile.Field,
      (firstResidualCell IRSProfile.Field gamma QA QB).card <
        residualStageOne.regularCountCap + firstResidualSingularCeiling := by
    intro gamma
    exact firstResidualCell_count_lt QA QB QC gamma hQA_ne hQB_ne hboxA hboxB
  have hres2_bound : ∀ gamma : IRSProfile.Field,
      (secondResidualCell IRSProfile.Field gamma QA QB QC).card <
        residualStageTwo.regularCountCap + secondResidualSingularCeiling := by
    intro gamma
    exact secondResidualCell_count_lt QA QB QC gamma hQA_ne hQB_ne hQC_ne hboxA hboxB hboxC
  have htotal : ∀ gamma : IRSProfile.Field,
      (selectedSeedSet IRSProfile.Field gamma QA QB QC).card < promotedBudget := by
    intro gamma
    have hpart := selectedSeedSet_card_eq_sum IRSProfile.Field gamma QA QB QC
    have hsum :
        (fixedCell IRSProfile.Field gamma QA QB QC).card +
            (firstResidualCell IRSProfile.Field gamma QA QB).card +
            (secondResidualCell IRSProfile.Field gamma QA QB QC).card <
          fixedCost +
            (residualStageOne.regularCountCap + firstResidualSingularCeiling) +
            (residualStageTwo.regularCountCap + secondResidualSingularCeiling) := by
      omega
    have hle :
        fixedCost +
            (residualStageOne.regularCountCap + firstResidualSingularCeiling) +
            (residualStageTwo.regularCountCap + secondResidualSingularCeiling) ≤
          promotedBudget := by
      have htot := totalCost_lt_promotedBudget
      omega
    omega
  refine ⟨QA, QB, QC, ?_⟩
  intro gamma P support hP hcard hvalues
  have hbranch := huniv gamma P support hP hcard hvalues
  have hcard_bound := htotal gamma
  omega

end

end ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research
