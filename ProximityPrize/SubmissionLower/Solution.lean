import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6423

/-!
Model label: gpt-5.
Exact lower-track entrypoint for the isolated 64.23 research assembly.
This file is not installed in the official checkout. Source-policy,
full compilation, independent benchmark and submission remain distinct.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6423 308067 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6423.protocolClaim6423

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
