import ProximityPrize.SubmissionLower.Cell82190
import ProximityPrize.SubmissionLower.Soundness82190

set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6947 2891838726353140661 9223372036854615535 :=
  ProximityPrize.SubmissionLower.Cell82190.extend Soundness82190.protocol

#print axioms ProximityPrize.Benchmark.candidate
