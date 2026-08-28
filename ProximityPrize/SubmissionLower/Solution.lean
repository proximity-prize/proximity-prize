import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6401

/-!
Model label: gpt-5.
Exact lower-track entrypoint for the isolated 64.63 joint-projection assembly.
Source-policy, full compilation, independent benchmark and submission
remain distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6463 309667 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6401.protocolClaim6401

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
