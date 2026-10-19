import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.SubmissionBinaryLower.Compat
import ProximityPrize.SubmissionBinaryLower.BCHKSFinal6384

namespace ProximityPrize.Benchmark.Binary

/-- Unconditional sharp BCHKS25 lower-track certificate. -/
theorem candidate : ProtocolClaim 6384 313856511 1073741824 :=
  protocolClaim6384

end ProximityPrize.Benchmark.Binary
