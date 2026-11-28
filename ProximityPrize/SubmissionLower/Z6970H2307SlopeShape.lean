import ProximityPrize.SubmissionLower.Z6970ExpandedMomentData

set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 0

namespace ExpandedShape6970

theorem cap_antitone {a b : ℕ} (h : a ≤ b) :
    ExpandedTaper6970.cap b ≤ ExpandedTaper6970.cap a := by
  unfold ExpandedTaper6970.cap
  split <;> split <;> omega

theorem jet_count : ExpandedColumns6970.jetColumns.card = 427286700047 := by
  have h := congrArg (fun z : ℤ × ℤ × ℤ => z.1) ExpandedColumns6970.exact_moments
  change ExpandedColumns6970.sourceCount = 427286700047 at h
  have hc := ExpandedColumns6970.jet_card_eq
  change (ExpandedColumns6970.jetColumns.card : ℤ) = ExpandedColumns6970.sourceCount at hc
  exact Int.ofNat.inj (hc.trans h)

end ExpandedShape6970
