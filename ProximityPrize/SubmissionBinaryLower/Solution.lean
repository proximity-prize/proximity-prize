import ProximityPrize.Benchmark.BinaryTargetLower
import ProximityPrize.SubmissionBinaryLower.Every6402Bucket
import ProximityPrize.SubmissionBinaryLower.B6402BankReduction

namespace ProximityPrize.Benchmark.Binary

/-- The binary 64.02-bit certificate at 1,482,750 agreements. -/
theorem candidate : ProtocolClaim 6402 78643482 268435456 :=
  ProximityPrize.SubmissionBinaryLower.B6402BankReduction.protocol
    (fun i q h => by
      rcases h with rfl|rfl
      · exact Binary6402Dispatch.every_1 i
      · exact Binary6402Dispatch.every_2 i)

end ProximityPrize.Benchmark.Binary

#print axioms ProximityPrize.Benchmark.Binary.candidate
