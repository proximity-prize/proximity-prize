import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingClosure6732Research

/-!
Exact lower-track entrypoint for the unconditional three-interpolant,
recursive-GCD score-67.33 assembly with an independent seedless Lambda
bound. Source-policy, kernel compilation, and Yukon validation remain
distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6733 10251903 33554432 :=
  ProximityPrize.SubmissionLower.ContactMovingClosure6732Research.protocolClaim6732

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
