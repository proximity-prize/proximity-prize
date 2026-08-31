import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research

 











namespace ProximityPrize.SubmissionLower
namespace ContactRouterUniformCaps6750Research

set_option autoImplicit false

 
def upstreamCap : Nat := 381688758681478

 


def hardAnchoredCap : Nat := 269668626181063029

 
def hardThirdCap : Nat := 7629767247944

 
def hardTotalCap : Nat := upstreamCap + hardAnchoredCap + hardThirdCap

 

def pairedEasyTotalCap : Nat := 274979443452684031

 


def easyDiagonalCap : Nat := 274979775394674415

theorem cap_values :
    hardTotalCap = 270057944706992451 ∧
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
      4922782176856674 := by
  decide

theorem easy_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - pairedEasyTotalCap =
      1283431165094 := by
  decide

theorem easy_diagonal_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - easyDiagonalCap =
      951489174710 := by
  decide

end ContactRouterUniformCaps6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.hardTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.pairedEasyTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.easyDiagonalCap_lt_mcaBudget
