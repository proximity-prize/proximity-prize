import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6733Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
open ContactTwoTailParameters6733Research
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def residualStageOne:UnequalParameters:=
  ⟨262144,131071,182052,112,25,1242,56,12,19688⟩
def residualStageTwo:UnequalParameters:=
  ⟨262144,131071,182052,56,12,1242,59,11,624668⟩
def pivotB:TightParameters:=
  ⟨262144,131071,182052,14746212,1242,25⟩
def pivotGcd12:TightParameters:=
  ⟨262144,131071,182052,7464132,1242,12⟩
theorem residual_stage_ceilings:
    residualStageOne.regularCountCap+pivotB.countCap+1=
      firstResidualRegularCost+firstResidualSingularCost∧
    residualStageTwo.regularCountCap+pivotGcd12.countCap+1=
      secondResidualRegularCost+secondResidualSingularCost:=by
  decide
theorem ledger_identifications:
    residualStageOne.regularCountCap=firstResidualRegularCost∧
    pivotB.countCap+1=firstResidualSingularCost∧
    residualStageTwo.regularCountCap=secondResidualRegularCost∧
    pivotGcd12.countCap+1=secondResidualSingularCost:=by
  decide
end ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6733Research
