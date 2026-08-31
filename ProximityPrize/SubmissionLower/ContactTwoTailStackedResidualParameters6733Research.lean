import ProximityPrize.SubmissionLower.ContactRecursiveResidualStages6656Research
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedResidualParameters6733Research
open ContactParameters6600Research ContactSingularLedger6600Research
open ContactRecursiveResidualStages6656Research ContactTightSingularLedgerResearch
open ContactTwoTailParameters6733Research
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
def residualStageOne:UnequalParameters:=
  ⟨262144,131071,181717,180,38,1000,88,20,400000⟩
def residualStageTwo:UnequalParameters:=
  ⟨262144,131071,181717,88,20,1000,98,18,1600000⟩
def pivotB:TightParameters:=
  ⟨262144,131071,181717,23623210,1000,38⟩
def pivotGcd12:TightParameters:=
  ⟨262144,131071,181717,11629888,1000,20⟩
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
