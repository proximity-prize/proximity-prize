import ProximityPrize.SubmissionLower.PortfolioSource6815
namespace ProximityPrize.SubmissionLower.PortfolioSource6815
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem dimension_of_counts (p : Parameters) (Kdim C R : ℕ)
    (hsB : 2*p.s≤p.B) (hBm : p.B≤p.m) (hU : p.m+p.s≤p.U)
    (hL : p.m+p.B+p.s≤p.L) (hUT : p.U≤p.L)
    (hcaps : ∀ h, h≤p.s → p.U≤(p.cutoff h+p.B-1)/131071)
    (hC : SecondJetRelaxedGlobalCounts.coefficientCount p.cutoff 131071 p.L p.B p.s p.U=C)
    (hR : SecondJetRelaxedCounts.rankBound p.m p.L p.B p.s p.U=R)
    (hfit : Kdim+262144*R≤C) : Dimension p Kdim := by
  unfold Dimension
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ hsB hBm hU hL hcaps,
    SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUT,hR,hC]
  exact hfit

end ProximityPrize.SubmissionLower.PortfolioSource6815
