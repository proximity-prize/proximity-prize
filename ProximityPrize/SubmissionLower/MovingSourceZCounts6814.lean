import ProximityPrize.SubmissionLower.MovingSourcePacketCount6814

/-! Kernel-checked source-31 dimensions at 181255 agreements.
Only closed coefficient/rank formulas are evaluated, not coefficient spaces. -/
namespace ProximityPrize.SubmissionLower.MovingSourceZCounts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  130*181255-SecondJetRelaxedDifferentiation.reserve 6 8 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤24) : 177≤(cutoff h+53-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3429 53 24 177=3830167918600970 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 130 3429 53 24 177=14610919708 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3429 53 24 177)=3830167918600970 := by
  rw [card_index_closed cutoff 131071 3429 53 24 177 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 130 3429 53 24 177
    (fun h => (cutoff h+53-1)/131071)=14610919708 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 130 3429 53 24 177 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    2982667018+262144*SecondJetRelaxedGlobalMap.rankBound 130 3429 53 24 177
      (fun h => (cutoff h+53-1)/131071)=Fintype.card (Index cutoff 131071 3429 53 24 177) := by
  rw [source_rank,source_card]

#print axioms source_nullity
end ProximityPrize.SubmissionLower.MovingSourceZCounts6814
