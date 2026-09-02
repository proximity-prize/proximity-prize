import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelS2
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel S2 = (500, 1000000, 150) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 500 1000000 150 = 14383345717650 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 500 1000000 150 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 90760000 131071 1000000 150 - 262144 * localRankBound 500 1000000 150 = 26099605139687297 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 90760000 131071 1000000 150 693 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelS2
