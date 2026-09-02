import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L3 = (2320, 100000, 720) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 2320 100000 720 = 144846693595800 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 2320 100000 720 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 421126400 131071 100000 720 3213 = 38179057646132098752 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 421126400 131071 100000 720 3213 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 421126400 131071 100000 720 - 262144 * localRankBound 2320 100000 720 = 208366000154703552 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 421126400 131071 100000 720 3213 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL3
