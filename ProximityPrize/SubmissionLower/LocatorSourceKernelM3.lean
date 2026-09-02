import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelM3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel M3 = (3100, 300000, 950) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 3100 300000 950 = 1032289695622850 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3100 300000 950 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 562712000 131071 300000 950 4294 = 272488465182259092673 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 562712000 131071 300000 950 4294 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 562712000 131071 300000 950 - 262144 * localRankBound 3100 300000 950 = 1879915212902702273 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 562712000 131071 300000 950 4294 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelM3
