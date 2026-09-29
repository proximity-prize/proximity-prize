import ProximityPrize.SubmissionLower.MovingSourcePacketCount6814

/-! Kernel-checked dimensions for lower-total Z source 7.
Only the existing closed count/rank formulas are evaluated. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ7Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  114*181255-SecondJetRelaxedDifferentiation.reserve 5 7 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤21) : 154≤(cutoff h+47-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3043 47 21 154=2066370262589177 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 114 3043 47 21 154=7882576304 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3043 47 21 154)=2066370262589177 := by
  rw [card_index_closed cutoff 131071 3043 47 21 154 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 114 3043 47 21 154
    (fun h => (cutoff h+47-1)/131071)=7882576304 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 114 3043 47 21 154 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    179953401+262144*SecondJetRelaxedGlobalMap.rankBound 114 3043 47 21 154
      (fun h => (cutoff h+47-1)/131071)=Fintype.card (Index cutoff 131071 3043 47 21 154) := by
  rw [source_rank,source_card]

#print axioms source_nullity
end ProximityPrize.SubmissionLower.MovingSourceLowZ7Counts6814
