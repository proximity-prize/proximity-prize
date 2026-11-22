import ProximityPrize.SubmissionLower.FrontRank282268
import ProximityPrize.SubmissionLower.FrontRank382268
import ProximityPrize.SubmissionLower.FrontRank482268
import ProximityPrize.SubmissionLower.FrontRank582268

set_option Elab.async false

namespace Front82268
open ProximityPrize.Benchmark

/-- The uniform core counts through height 2535 and from 2536 suffice for the protocol. -/
theorem of_core_counts (low : c6) (high : c7) :
    ProtocolClaim 6955 ProtocolTarget82268.radiusNumerator ProtocolTarget82268.radiusDenominator :=
  of_children Front82268_1.proof Front82268_2.proof
    (Front82268_3.of_children Front82268_3_1.proof Front82268_3_2.proof)
    (Front82268_4.of_children Front82268_4_1.proof Front82268_4_2.proof)
    Front82268_5.proof low high

#print axioms of_core_counts
end Front82268
