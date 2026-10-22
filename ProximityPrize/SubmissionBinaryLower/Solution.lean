import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.SubmissionBinaryLower.Compat
import ProximityPrize.SubmissionBinaryLower.BCHKSFinal6400

namespace ProximityPrize.Benchmark.Binary

/-- Unconditional sharp BCHKS25 lower-track certificate. -/
theorem candidate : ProtocolClaim 6400 314491700 1073741824 :=
  protocolClaim6400

end ProximityPrize.Benchmark.Binary
