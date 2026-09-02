import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL4
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L4 = (1600, 200000, 480) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 1600 200000 480 = 93335513436880 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1600 200000 480 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 290432000 131071 200000 480 2216 = 24637034143949184360 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 290432000 131071 200000 480 2216 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 290432000 131071 200000 480 - 262144 * localRankBound 1600 200000 480 = 169689309551713640 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 290432000 131071 200000 480 2216 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL4
