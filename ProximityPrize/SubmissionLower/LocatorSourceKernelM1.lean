import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelM1
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel M1 = (2600, 300000, 800) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 2600 300000 800 = 611531114395200 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 2600 300000 800 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 471952000 131071 300000 800 3601 = 161447664403780924200 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 471952000 131071 300000 800 3601 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 471952000 131071 300000 800 - 262144 * localRankBound 2600 300000 800 = 1138451951765615400 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 471952000 131071 300000 800 3601 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelM1
