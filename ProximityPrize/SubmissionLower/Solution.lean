import ProximityPrize.SubmissionLower.Cell82170
import ProximityPrize.SubmissionLower.Soundness82170

set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6945 2891135038911389412 9223372036854696499 :=
  ProximityPrize.SubmissionLower.Cell82170.extend Soundness82170.protocol
