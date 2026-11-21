import ProximityPrize.SubmissionLower.KoalaScalarList
import ProximityPrize.SubmissionLower.FrontRank282200
import ProximityPrize.SubmissionLower.FrontRank382200
import ProximityPrize.SubmissionLower.FrontRank482200
import ProximityPrize.SubmissionLower.FrontRank582200
import ProximityPrize.SubmissionLower.Cell82200

set_option Elab.async false

namespace Front82200
open ProximityPrize.Benchmark

/-- The uniform core counts through height 2413 and from 2414 suffice for the protocol. -/
theorem of_core_counts (low : c6) (high : c7) :
    ProtocolClaim 6954 ProtocolTarget82200.radiusNumerator ProtocolTarget82200.radiusDenominator :=
  of_children KoalaScalarList.scalar_list Front82200_1.proof Front82200_2.proof
    (Front82200_3.of_children Front82200_3_1.proof Front82200_3_2.proof)
    (Front82200_4.of_children Front82200_4_1.proof Front82200_4_2.proof)
    Front82200_5.proof low high

theorem of_core_counts_at_maximal_radius (low : c6) (high : c7) :
    ProtocolClaim 6954 ProximityPrize.SubmissionLower.Cell82200.p ProximityPrize.SubmissionLower.Cell82200.q :=
  ProximityPrize.SubmissionLower.Cell82200.extend (of_core_counts low high)

#print axioms of_core_counts
#print axioms of_core_counts_at_maximal_radius
end Front82200
