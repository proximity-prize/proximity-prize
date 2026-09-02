import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL1
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel L1 = (1200, 100000, 360) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 1200 100000 360 = 19672498204460 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1200 100000 360 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 217824000 131071 100000 360 - 262144 * localRankBound 1200 100000 360 = 32824016747150030 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 217824000 131071 100000 360 1662 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelL1
