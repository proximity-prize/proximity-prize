import ProximityPrize.SubmissionLower.Z6969Pack0796
import ProximityPrize.SubmissionLower.Z6970HeightJoin

set_option autoImplicit false

namespace Research6970.Composition

open ProximityPrize.Benchmark

theorem candidate_of_low (low : HeightJoin.Low) :
    ProtocolClaim 6970 2899720025701049676 9223372036854649837 := by
  apply Research6969.ProfileEndpoint.of_height_counts
  · exact low
  · intro u deleted M Γ F lo hi
    exact HeightJoin.high M F lo hi

end Research6970.Composition

#print axioms Research6970.Composition.candidate_of_low
