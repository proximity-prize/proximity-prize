import ProximityPrize.SubmissionLower.Final50GeoFinish
import ProximityPrize.SubmissionLower.Front50ProtocolCore

set_option Elab.async false
namespace Final50Protocol
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Cell82219 (p q)

/-- The mixed intersection estimate at height 2,404 suffices for the complete protocol bound. -/
theorem of_allocation (allocation : Final50Geo.Allocation) : ProtocolClaim 6950 p q :=
  Front50Direct.of_low fun _ _ M _ F lo hi => Final50Geo.count_of_allocation allocation M F lo hi

#print axioms of_allocation
end Final50Protocol
