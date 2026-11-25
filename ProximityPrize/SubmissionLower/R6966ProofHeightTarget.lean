import ProximityPrize.SubmissionLower.Front6966Rank3
import ProximityPrize.SubmissionLower.Front6966Rank4
import ProximityPrize.SubmissionLower.Front6966Rank5

set_option Elab.async false

namespace Research6966.HeightTarget
open ProximityPrize.Benchmark

/-- The rank-front, list, radius and binary error budget are all discharged.
The remaining count arguments are precisely the low and high P1 families. -/
theorem of_height_counts (low:Front6966.c6) (high:Front6966.c7) :
    ProtocolClaim 6966 ProtocolProfile.p ProtocolProfile.q :=
  Front6966.of_children R6966ListBridge.scalar_list Front6966_1.proof Front6966_2.proof
    (Front6966_3.of_children Front6966_3_1.proof Front6966_3_2.proof)
    (Front6966_4.of_children Front6966_4_1.proof Front6966_4_2.proof)
    Front6966_5.proof low high

#print axioms of_height_counts
end Research6966.HeightTarget
