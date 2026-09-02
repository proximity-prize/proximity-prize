import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelT10k
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel T10k = (540, 10000, 170) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 540 10000 170 = 183265775280 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 540 10000 170 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 98020800 131071 10000 170 748 = 48098759564045697 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 98020800 131071 10000 170 748 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 98020800 131071 10000 170 - 262144 * localRankBound 540 10000 170 = 56736169045377 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 98020800 131071 10000 170 748 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelT10k
