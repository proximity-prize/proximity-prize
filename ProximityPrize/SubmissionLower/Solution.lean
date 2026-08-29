import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6630Research

/-!
Exact lower-track entrypoint for the unconditional cumulative-flag,
adaptive-YZ-projection score-66.75 assembly with seedless fixed-centre Lambda.
Source-policy, kernel compilation,
and Yukon validation remain distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6675 318083 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6630Research.protocolClaim6630

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
