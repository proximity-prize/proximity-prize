import ProximityPrize.SubmissionLower.LowerProof

/-! Derived from nethoxa PR508, immutable d32c3ea60f26bc50bb858e012551118b7b74456a.
The second-jet construction and finite certificate are credited to nethoxa;
inherited closure and phase work credit jsign PR506 and the promoted lineage.
This derivative replaces copied Mathlib ports with pinned library imports. -/

namespace ProximityPrize.Benchmark
theorem candidate : ProtocolClaim 6804 10341375 33554432 :=
  ProximityPrize.SubmissionLower.Lower80791.CompressedClaim.protocolClaim
end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
