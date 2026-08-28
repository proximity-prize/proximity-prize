import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6719Research

/-! . -/
namespace ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6719Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def residualStageOne : UnequalParameters :=
  ⟨262144, 131071, 182189, 98, 22, 1006, 51, 10, 22092⟩
def residualStageTwo : UnequalParameters :=
  ⟨262144, 131071, 182189, 51, 10, 1006, 98, 22, 1006⟩
def pivotB : TightParameters := ⟨262144, 131071, 182189, 12935419, 1006, 22⟩
def pivotGcd12 : TightParameters := ⟨262144, 131071, 182189, 6740993, 1006, 10⟩
def firstResidualSingularCeiling : ℕ :=
  ContactMovingParameters6719Research.firstResidualSingularCeiling
def secondResidualSingularCeiling : ℕ :=
  ContactMovingParameters6719Research.secondResidualSingularCeiling

theorem residual_stage_ceilings :
    residualStageOne.regularCountCap + pivotB.countCap + 1 =
      95921187844877 + firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap + pivotGcd12.countCap + 1 =
      5708294799780 + secondResidualSingularCeiling := by decide

/-- . -/
theorem ledger_identifications :
    residualStageOne.regularCountCap = ContactMovingParameters6719Research.firstResidualRegularCost ∧
    pivotB.countCap + 1 = ContactMovingParameters6719Research.firstResidualSingularCeiling ∧
    residualStageTwo.regularCountCap = ContactMovingParameters6719Research.secondResidualRegularCost ∧
    pivotGcd12.countCap + 1 = ContactMovingParameters6719Research.secondResidualSingularCeiling := by
  decide

end ProximityPrize.SubmissionLower.ContactMovingStackedResidualParameters6719Research
