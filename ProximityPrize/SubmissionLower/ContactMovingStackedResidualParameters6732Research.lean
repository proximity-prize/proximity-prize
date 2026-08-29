import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6732Research

open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182060, 112, 25, 1225, 59, 11, 48000⟩

def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182060, 59, 11, 1225, 55, 12, 91386⟩

def pivotB : TightParameters :=
  ⟨262144, 131071, 182060, 14746860, 1225, 25⟩

def pivotGcd12 : TightParameters :=
  ⟨262144, 131071, 182060, 7828580, 1225, 11⟩

def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.firstResidualSingularCeiling

def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6732Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      269092561863969 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      163716005926328 + secondResidualSingularCeiling := by
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
