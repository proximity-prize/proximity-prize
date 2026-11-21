import ProximityPrize.SubmissionLower.Final50SharedProtocol
import ProximityPrize.SubmissionLower.Shared50Count

set_option Elab.async false
namespace Soundness82219

open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Cell82219 (p q)

/-- The reduction is safe at the upper end of the 82,219-error cell. -/
theorem protocol : ProtocolClaim 6950 p q :=
  Final50Protocol.of_shared Shared50Count.proof

#print axioms protocol
end Soundness82219
