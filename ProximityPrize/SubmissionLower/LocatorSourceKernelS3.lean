import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelS3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel S3 = (810, 350000, 243) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 810 350000 243 = 21307937367528 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 810 350000 243 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 147031200 131071 350000 243 - 262144 * localRankBound 810 350000 243 = 40160939066613289 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 147031200 131071 350000 243 1122 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelS3
