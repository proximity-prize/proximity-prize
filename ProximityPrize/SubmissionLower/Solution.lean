import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6600Research

/-!
Exact lower-track entrypoint for the unconditional adaptive-projection score-66
assembly. Source-policy, kernel compilation, and Yukon validation remain
distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6618 315835 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6600Research.protocolClaim6600

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
