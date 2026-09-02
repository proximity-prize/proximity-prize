import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL1
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L1 = (1200, 100000, 360) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 1200 100000 360 = 19672498204460 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1200 100000 360 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 217824000 131071 100000 360 1662 = 5189851386057112270 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 217824000 131071 100000 360 1662 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 217824000 131071 100000 360 - 262144 * localRankBound 1200 100000 360 = 32824016747150030 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 217824000 131071 100000 360 1662 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL1
