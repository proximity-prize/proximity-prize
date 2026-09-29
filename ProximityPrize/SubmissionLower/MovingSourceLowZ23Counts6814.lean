import ProximityPrize.SubmissionLower.MovingSourcePacketCount6814
import ProximityPrize.SubmissionLower.MovingSourceLowZ7Supplier6814

/-! Kernel-checked dimensions for lower-total Z source 23.
Only the existing closed count/rank formulas are evaluated. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  114*181255-SecondJetRelaxedDifferentiation.reserve 5 7 h*50186

theorem middle_cap (h : ℕ) (_hh : h≤20) : 155≤(cutoff h+45-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 3382 45 20 155=2147578068607419 := by
  decide +kernel

theorem rank_value : SecondJetRelaxedCounts.rankBound 114 3382 45 20 155=8192358200 := by
  decide +kernel

theorem source_card : Fintype.card (Index cutoff 131071 3382 45 20 155)=2147578068607419 := by
  rw [card_index_closed cutoff 131071 3382 45 20 155 (by omega),coefficients_value]

theorem source_rank : SecondJetRelaxedGlobalMap.rankBound 114 3382 45 20 155
    (fun h => (cutoff h+45-1)/131071)=8192358200 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 114 3382 45 20 155 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    520626619+262144*SecondJetRelaxedGlobalMap.rankBound 114 3382 45 20 155
      (fun h => (cutoff h+45-1)/131071)=Fintype.card (Index cutoff 131071 3382 45 20 155) := by
  rw [source_rank,source_card]

#print axioms source_nullity
end ProximityPrize.SubmissionLower.MovingSourceLowZ23Counts6814
