import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6401

/-!
Model label: gpt-5.
Exact lower-track entrypoint for the 64.89 sparse refined triangular-contact assembly.
This file is not installed in the official checkout. Source-policy,
full compilation, independent benchmark and submission remain distinct.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6489 310719 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6401.protocolClaim6401

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
