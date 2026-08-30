import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocatorClosure
namespace ProximityPrize.Benchmark
set_option maxHeartbeats 0 in
theorem candidate : ProtocolClaim 6744 10265855 33554432 :=
  ProximityPrize.SubmissionLower.LocatorClosure.protocolClaim6744
end ProximityPrize.Benchmark
