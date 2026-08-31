import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingSeedless6750Research

 











namespace ProximityPrize.SubmissionLower
namespace ContactRouterUniformCaps6750Research

set_option autoImplicit false

 
def upstreamCap : Nat := 1711100000000000

 


def hardAnchoredCap : Nat := 272700000000000000

 
def hardThirdCap : Nat := 10200000000000

 
def hardTotalCap : Nat := upstreamCap + hardAnchoredCap + hardThirdCap

 

def pairedEasyTotalCap : Nat := 274979443452684031

 


def easyDiagonalCap : Nat := 273638324128818589

theorem cap_values :
    hardTotalCap = 274421300000000000 ∧
      pairedEasyTotalCap = 274979443452684031 ∧
      easyDiagonalCap = 273638324128818589 := by
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
      559426883849125 := by
  decide

theorem easy_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - pairedEasyTotalCap =
      1283431165094 := by
  decide

theorem easy_diagonal_slack_exact :
    ContactMovingSeedless6750Research.mcaBudget - easyDiagonalCap =
      1342402755030536 := by
  decide

end ContactRouterUniformCaps6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.hardTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.pairedEasyTotalCap_lt_mcaBudget
#print axioms ProximityPrize.SubmissionLower.ContactRouterUniformCaps6750Research.easyDiagonalCap_lt_mcaBudget
