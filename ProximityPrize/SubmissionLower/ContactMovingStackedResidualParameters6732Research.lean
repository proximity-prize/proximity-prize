import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182032, 105, 22, 1340, 65, 12, 20000⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182032, 65, 12, 1340, 66, 12, 20000⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182032, 13834432, 1340, 22⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182032, 8555504, 1340, 12⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      100266553100671 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      43359121462115 + secondResidualSingularCeiling := by
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
