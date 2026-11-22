import ProximityPrize.SubmissionLower.FrontRank282200
import ProximityPrize.SubmissionLower.FrontRank382200
import ProximityPrize.SubmissionLower.FrontRank482200
import ProximityPrize.SubmissionLower.FrontRank582200
import ProximityPrize.SubmissionLower.Cell82200

set_option Elab.async false

namespace Front82200
open ProximityPrize.Benchmark

/-- The scalar list and the uniform core counts suffice for the protocol at 82,239 errors. -/
theorem of_core_counts (hlist : CJ0.ScalarList agreement listCap) (low : c6) (high : c7) :
    ProtocolClaim 6952 ProtocolTarget82200.radiusNumerator ProtocolTarget82200.radiusDenominator :=
  of_children hlist Front82200_1.proof Front82200_2.proof
    (Front82200_3.of_children Front82200_3_1.proof Front82200_3_2.proof)
    (Front82200_4.of_children Front82200_4_1.proof Front82200_4_2.proof)
    Front82200_5.proof low high

theorem of_core_counts_at_maximal_radius (hlist : CJ0.ScalarList agreement listCap)
    (low : c6) (high : c7) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p ProximityPrize.SubmissionLower.Cell82200.q :=
  ProximityPrize.SubmissionLower.Cell82200.extend (of_core_counts hlist low high)

/-- 69.52 staging (82,239 errors, agreement 179,905): the scalar list stays a hypothesis until lambda's 179,905 list lands. -/
theorem of_low_high (hlist : CJ0.ScalarList agreement listCap) (low : c6) (high : c7) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p ProximityPrize.SubmissionLower.Cell82200.q :=
  of_core_counts_at_maximal_radius hlist low high

/-- Same, with the high side split at `h0` so a middle band can stay the single open hypothesis. -/
theorem of_low_mid_high (hlist : CJ0.ScalarList agreement listCap) (h0 : ℤ) (low : c6)
    (mid : ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
      lowCutoff + 1 ≤ M.overhead → M.overhead ≤ h0 → Γ.card ≤ highCap)
    (high : ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
      h0 + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) → Γ.card ≤ highCap) :
    ProtocolClaim 6952 ProximityPrize.SubmissionLower.Cell82200.p ProximityPrize.SubmissionLower.Cell82200.q :=
  of_low_high hlist low fun u deleted M Γ F lo hi => by
    by_cases h : M.overhead ≤ h0
    · exact mid u deleted M Γ F lo h
    · exact high u deleted M Γ F (by omega) hi

#print axioms of_core_counts
#print axioms of_core_counts_at_maximal_radius
#print axioms of_low_high
#print axioms of_low_mid_high
end Front82200
