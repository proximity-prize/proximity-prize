import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelH4
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel H4 = (1000, 2000000, 300) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 1000 2000000 300 = 229040327786550 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1000 2000000 300 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 181520000 131071 2000000 300 1385 = 60493817742652884415 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 181520000 131071 2000000 300 1385 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 181520000 131071 2000000 300 - 262144 * localRankBound 1000 2000000 300 = 452270055375521215 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 181520000 131071 2000000 300 1385 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelH4
