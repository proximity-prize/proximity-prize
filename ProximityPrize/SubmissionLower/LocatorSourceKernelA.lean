import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelA
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel A = (76, 130000, 22) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 76 130000 22 = 6740780706 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 76 130000 22 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 13795520 131071 130000 22 - 262144 * localRankBound 76 130000 22 = 255124945551 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 13795520 131071 130000 22 106 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelA
