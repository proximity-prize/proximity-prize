import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactProtocol6533

/-!
Exact lower-track entrypoint for the characteristic-free full-triangle common-shear 65.67
assembly.  Source-policy, kernel compilation, and Yukon validation remain
distinct checks.
-/

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6567 313823 1048576 :=
  ProximityPrize.SubmissionLower.ContactProtocol6533.protocolClaim6533

end ProximityPrize.Benchmark

#print axioms ProximityPrize.Benchmark.candidate
