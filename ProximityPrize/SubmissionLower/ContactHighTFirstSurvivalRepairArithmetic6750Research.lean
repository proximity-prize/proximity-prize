import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactHighTDerivativeRouter6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactHighTFirstSurvivalRepairArithmetic6750Research

open ContactHighTDerivativeRouter6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactRouterCellCosts6750Research
open ContactTwoTailParameters6750Research

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

 

def firstSurvivalLowSliceCodim (T YS S j : Nat) : Nat :=
  j * 50814 * nestedFiveCapChannelCount T YS S

 



theorem firstSurvivalLowSliceCodim_le_derivativeFailureResidual
    {T YS S j : Nat} (hT : T ≤ 8) (hYS : T ≤ YS) (hS : T ≤ S)
    (hj : j ≤ 14) :
    firstSurvivalLowSliceCodim T YS S j ≤
      derivativeFailureResidual T YS S j := by
  have hchannels : nestedFiveCapChannelCount T YS S =
      nestedFiveCapChannelCount T T T := by
    unfold nestedFiveCapChannelCount
    rw [min_eq_left hYS, min_self]
    apply Finset.sum_congr rfl
    intro y hy
    have hyT : y ≤ T := by
      simp only [Finset.mem_range] at hy
      omega
    have hsub : T - y ≤ YS - y := Nat.sub_le_sub_right hYS y
    rw [min_eq_left hsub, min_eq_right (by omega)]
    simp only [min_self, min_eq_right (Nat.sub_le T y)]
  have hfailure : derivativeFailureResidual T YS S j =
      derivativeFailureResidual T T T j := by
    unfold derivativeFailureResidual
    rw [min_eq_left hYS, min_self]
    apply Finset.sum_congr rfl
    intro u hu
    have huT : u ≤ T := by
      simp only [Finset.mem_range] at hu
      omega
    rw [min_eq_right (huT.trans hS), min_eq_right huT]
  unfold firstSurvivalLowSliceCodim
  rw [hchannels, hfailure]
  have hcheck : ∀ (TT : Fin 9) (jj : Fin 15),
      firstSurvivalLowSliceCodim TT.val TT.val TT.val jj.val ≤
        derivativeFailureResidual TT.val TT.val TT.val jj.val := by
    decide
  exact hcheck ⟨T, by omega⟩ ⟨j, by omega⟩

 

def smallProfileBEquationCap : Nat :=
  cellRegularCost 9 9 8 +
    (cellTightProfile profileB.weightedCap 9 8).countCap

theorem smallProfileBEquationCap_value :
    smallProfileBEquationCap = 40049866771028 := by
  decide

def repairedHighTCap : Nat :=
  270096665443142692 + smallProfileBEquationCap

theorem repairedHighTCap_value :
    repairedHighTCap = 270136715309913720 := by
  decide

theorem repairedHighTCap_lt_mcaBudget :
    repairedHighTCap < ContactMovingSeedless6750Research.mcaBudget := by
  decide

theorem repairedHighTCap_slack :
    ContactMovingSeedless6750Research.mcaBudget - repairedHighTCap =
      4844011592772506 := by
  decide

end ContactHighTFirstSurvivalRepairArithmetic6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactHighTFirstSurvivalRepairArithmetic6750Research.firstSurvivalLowSliceCodim_le_derivativeFailureResidual
#print axioms ProximityPrize.SubmissionLower.ContactHighTFirstSurvivalRepairArithmetic6750Research.repairedHighTCap_lt_mcaBudget
