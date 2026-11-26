import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.SubmissionBinaryLower.B6401Main

set_option Elab.async false

namespace ProximityPrize.Benchmark.Binary

/-- Unconditional binary lower-track certificate at 64.01 induced bits. -/
theorem candidate : ProtocolClaim 6401 78633206 268435456 :=
  ProximityPrize.SubmissionBinaryLower.B6401Main.protocolClaim6401

end ProximityPrize.Benchmark.Binary
