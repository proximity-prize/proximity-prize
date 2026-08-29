import ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6670Research

/-!
# Actual recursive-GCD residual cells at score 67.40

The first cell uses the profile-B quotient as singular pivot and the profile-A
quotient as external proper cut.  The second uses the A/B-GCD quotient as
pivot and the profile-C quotient as cut.  The accepted asymmetric regular and
parameterized tight-singular providers close both cells; this module supplies
only their target-specific boxes, seed equations, and arithmetic gates.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps
open ContactRecursiveGCDResearch
open ContactStackedParameters6670Research
open ContactStackedSeedPartition6670Research
open ContactStackedBoxTransport6670Research
open ContactRecursiveResidualStages6670Research
open ContactStackedResidualCells6656Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

theorem firstResidualCell_count_lt
    (A B C : GlobalPoly) (gamma : IRSProfile.Field)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (45 * agreements) w 20000 14)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1450 23) :
    (firstResidualCell IRSProfile.Field gamma A B).card <
      residualStageOne.regularCountCap + firstResidualSingularCeiling := by
  have hreg := residualStageOne_count_lt A B gamma hA hB hboxA hboxB
  have hsing := pivotB_count_lt B gamma hB hboxB
  omega

theorem secondResidualCell_count_lt
    (A B C : GlobalPoly) (gamma : IRSProfile.Field)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (45 * agreements) w 20000 14)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1450 23)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (45 * agreements) w 50000 14) :
    (secondResidualCell IRSProfile.Field gamma A B C).card <
      residualStageTwo.regularCountCap + secondResidualSingularCeiling := by
  have hreg := residualStageTwo_count_lt A B C gamma hA hB hC hboxA hboxB hboxC
  have hsing := pivotGcd12_count_lt A B gamma hA hB hboxA hboxB
  omega

end

end ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research
