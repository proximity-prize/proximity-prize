import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelT30k
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel T30k = (570, 30000, 170) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 570 30000 170 = 630511727250 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 570 30000 170 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 103466400 131071 30000 170 - 262144 * localRankBound 570 30000 170 = 825486901846260 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 103466400 131071 30000 170 790 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelT30k
