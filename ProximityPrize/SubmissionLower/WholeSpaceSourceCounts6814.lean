import ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814

/-! Concrete dimensions for the single enlarged second-jet source.
Only the closed counting formulas are evaluated; the finite polynomial
space itself (208 trillion coefficients) is never enumerated. -/
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
open scoped BigOperators
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cutoff (h : ℕ) : ℕ :=
  72*181255-SecondJetRelaxedDifferentiation.reserve 2 3 h*50186

theorem middle_cap (h : ℕ) (hh : h ≤ 14) : 98 ≤ (cutoff h+31-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem coefficients_value :
    coefficientCount cutoff 131071 1700 31 14 98=208109695383786 := by
  decide +kernel

theorem rank_value :
    SecondJetRelaxedCounts.rankBound 72 1700 31 14 98=791483658 := by
  decide +kernel

theorem source_card :
    Fintype.card (Index cutoff 131071 1700 31 14 98)=208109695383786 := by
  rw [card_index_closed cutoff 131071 1700 31 14 98 (by omega),coefficients_value]

theorem source_rank :
    SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
      (fun h => (cutoff h+31-1)/131071)=791483658 := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 72 1700 31 14 98 _
    (by omega) (by omega) (by omega) (by omega) middle_cap,rank_value]

theorem source_nullity :
    627003341034+262144*SecondJetRelaxedGlobalMap.rankBound 72 1700 31 14 98
      (fun h => (cutoff h+31-1)/131071) ≤
        Fintype.card (Index cutoff 131071 1700 31 14 98) := by
  rw [source_rank,source_card]

#print axioms source_nullity
end ProximityPrize.SubmissionLower.WholeSpaceSourceCounts6814
