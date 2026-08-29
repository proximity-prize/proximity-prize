import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6719Research

/-! . -/
namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6719Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182180, 98, 22, 1019, 51, 10, 52037⟩
def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182180, 51, 10, 1019, 98, 22, 1019⟩
def pivotB : TightParameters := ⟨262144, 131071, 182180, 12934780, 1019, 22⟩
def pivotGcd12 : TightParameters := ⟨262144, 131071, 182180, 6740660, 1019, 10⟩
def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6719Research.firstResidualSingularCeiling
def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6719Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      224093416924844 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      5783076045166 + secondResidualSingularCeiling := by decide

/-- . -/
theorem ledger_identifications :
    residualStageOne.regularCountCap = ContactMovingParameters6719Research.firstResidualRegularCost ∧
    pivotB.countCap + 1 = ContactMovingParameters6719Research.firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap = ContactMovingParameters6719Research.secondResidualRegularCost ∧
    pivotGcd12.countCap + 1 = ContactMovingParameters6719Research.secondResidualSingularCeiling := by
  decide

end ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6719Research
