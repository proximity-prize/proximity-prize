import ProximityPrize.SubmissionLower.PartG076


section Compact_SecondJetRelaxedCounts
/-! The closed local rank expression used by the concrete interpolation receipts. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedCounts
open scoped BigOperators
open SecondJetRelaxedSourceCounts SecondJetRelaxedKernelCounts
noncomputable section
set_option autoImplicit false

def rankBound (m L B s U : ℕ) : ℕ := sourceCount m L B s U-kernelCount m L B s U

theorem rankBound_eq_closed (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hsB : 2*s ≤ B) (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    SecondJetRelaxedGlobalMap.rankBound m L B s U caps = rankBound m L B s U := by
  unfold SecondJetRelaxedGlobalMap.rankBound rankBound
  rw [card_source_closed m L B s U caps hsB hBm hU hL hcaps,
    card_kernel_sum m L B s U caps hBm hU hL hcaps]

variable {K : Type*} [Field K]
theorem local_rank_le_count (m L B s U : ℕ) (caps : ℕ → ℕ)
    (hsB : 2*s ≤ B) (hBm : B ≤ m) (hU : m+s ≤ U) (hL : m+B+s ≤ L)
    (hcaps : ∀ h, h ≤ s → U ≤ caps h) :
    Module.finrank K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range ≤
      rankBound m L B s U := by
  rw [← rankBound_eq_closed m L B s U caps hsB hBm hU hL hcaps]
  exact SecondJetRelaxedGlobalMap.local_rank_le_count m L B s U caps

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedCounts

end Compact_SecondJetRelaxedCounts
