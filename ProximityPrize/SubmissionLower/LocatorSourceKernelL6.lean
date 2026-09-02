import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL6
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L6 = (3900, 200000, 1200) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 3900 200000 1200 = 1368423036387800 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3900 200000 1200 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 707928000 131071 200000 1200 5402 = 360871493828872769700 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 707928000 131071 200000 1200 5402 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 707928000 131071 200000 1200 - 262144 * localRankBound 3900 200000 1200 = 2147605378029326500 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 707928000 131071 200000 1200 5402 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL6
