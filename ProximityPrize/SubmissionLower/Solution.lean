import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSFinal6400Conditional
import ProximityPrize.SubmissionLower.BCHKSAlignment6400

namespace ProximityPrize.Benchmark

/-- Frontier candidate. This file is activated only after the independent
`bchksAlignment6400` theorem has been supplied without forbidden axioms. -/
theorem candidate : ProtocolClaim 6400 307123 1048576 :=
  protocolClaim6400_of_alignment
    ProximityPrize.SubmissionLower.bchksAlignment6400

end ProximityPrize.Benchmark
