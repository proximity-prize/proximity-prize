import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.SubmissionBinaryLower.Compat
import ProximityPrize.SubmissionBinaryLower.P64C7High

namespace ProximityPrize.Benchmark.Binary

/-- Unconditional binary lower-track certificate at 64.00 induced bits. -/
theorem candidate : ProtocolClaim 6400 78622925 268435456 :=
  ProximityPrize.SubmissionBinaryLower.P64C7High.protocolClaim6400

end ProximityPrize.Benchmark.Binary
