import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182052, 112, 25, 1242, 59, 12, 6135⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182052, 59, 12, 1242, 56, 12, 19688⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182052, 14746212, 1242, 25⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182052, 7464132, 1242, 12⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      36914696494058 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      37840936333035 + secondResidualSingularCeiling := by
  decide

theorem ledger_identifications :
    residualStageOne.regularCountCap =
        ContactMovingParameters6732Research.firstResidualRegularCost ∧
    pivotB.countCap + 1 =
        ContactMovingParameters6732Research.firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap =
        ContactMovingParameters6732Research.secondResidualRegularCost ∧
    pivotGcd12.countCap + 1 =
        ContactMovingParameters6732Research.secondResidualSingularCeiling := by
  decide

end ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research
