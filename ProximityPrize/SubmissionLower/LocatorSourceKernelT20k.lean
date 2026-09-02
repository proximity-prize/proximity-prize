import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelT20k
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel T20k = (560, 20000, 170) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 560 20000 170 = 402402095160 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 560 20000 170 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 101651200 131071 20000 170 - 262144 * localRankBound 560 20000 170 = 427848492911895 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 101651200 131071 20000 170 776 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelT20k
