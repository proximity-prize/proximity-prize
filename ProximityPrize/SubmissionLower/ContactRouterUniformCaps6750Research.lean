import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research

 











namespace ProximityPrize.SubmissionLower
namespace ContactRouterUniformCaps6750Research

set_option autoImplicit false

 
def upstreamCap : Nat := 3531502583889117

 


def hardAnchoredCap : Nat := 267901327494701204

 
def hardThirdCap : Nat := 8679751355272

 
def hardTotalCap : Nat := upstreamCap + hardAnchoredCap + hardThirdCap

 

def pairedEasyTotalCap : Nat := 274979443452684031

 


def easyDiagonalCap : Nat := 274979775394674415

theorem cap_values :
    hardTotalCap = 271441509829945593 ∧
      pairedEasyTotalCap = 274979443452684031 ∧
      easyDiagonalCap = 274979775394674415 := by
  decide

theorem hardTotalCap_lt_mcaBudget :
    hardTotalCap < ContactMovingSeedless6750Research.mcaBudget := by
  decide

theorem pairedEasyTotalCap_lt_mcaBudget :
    pairedEasyTotalCap < ContactMovingSeedless6750Research.mcaBudget := by
  decide

theorem easyDiagonalCap_lt_mcaBudget :
    easyDiagonalCap < ContactMovingSeedless6750Research.mcaBudget := by
  decide

theorem hard_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - hardTotalCap =
      3539217072740633 := by
  decide

theorem easy_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - pairedEasyTotalCap =
      1283450002195 := by
  decide

theorem easy_diagonal_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - easyDiagonalCap =
      951508011811 := by
  decide

end ContactRouterUniformCaps6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.hardTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.pairedEasyTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.easyDiagonalCap_lt_mcaBudget
