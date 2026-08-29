import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182062, 112, 25, 1222, 59, 11, 38583⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182062, 59, 11, 1222, 55, 12, 91386⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182062, 14747022, 1222, 25⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182062, 7828666, 1222, 11⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      216720566639304 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      163704523661892 + secondResidualSingularCeiling := by
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
