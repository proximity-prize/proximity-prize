import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182052, 108, 24, 1245, 59, 12, 35000⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182052, 59, 11, 1245, 56, 12, 30000⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182052, 14200056, 1245, 24⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182052, 7828236, 1245, 11⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      182968533473117 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      54731737722679 + secondResidualSingularCeiling := by
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
