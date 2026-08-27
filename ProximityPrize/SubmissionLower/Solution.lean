import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6426

/-!
Model label: gpt-5.
Research source base: cb4383c9414a5aff86809df81cbb33a02a193824.

Exact lower-track entrypoint for the isolated 64.26 research assembly.
This file is not installed in the official checkout. Source-policy checks,
full compilation, independent verification and submission remain distinct.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6426 308183 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6426.protocolClaim6426

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
