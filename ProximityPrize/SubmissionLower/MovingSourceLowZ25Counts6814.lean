import ProximityPrize.SubmissionLower.MovingSourcePacketCount6814
import ProximityPrize.SubmissionLower.MovingSourceLowZ23Supplier6814

/-! Kernel-checked dimensions for lower-total Z source 25.
Only the existing closed count/rank formulas are evaluated. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  111*181255-SecondJetRelaxedDifferentiation.reserve 5 7 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤21) : 151≤(cutoff h+46-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3411 46 21 151=2116605519616735 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 111 3411 46 21 151=8074209199 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3411 46 21 151)=2116605519616735 := by
  rw [card_index_closed cutoff 131071 3411 46 21 151 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 111 3411 46 21 151
    (fun h => (cutoff h+46-1)/131071)=8074209199 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 111 3411 46 21 151 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    23354079+262144*SecondJetRelaxedGlobalMap.rankBound 111 3411 46 21 151
      (fun h => (cutoff h+46-1)/131071)=Fintype.card (Index cutoff 131071 3411 46 21 151) := by
  rw [source_rank,source_card]

#print axioms source_nullity
end ProximityPrize.SubmissionLower.MovingSourceLowZ25Counts6814
