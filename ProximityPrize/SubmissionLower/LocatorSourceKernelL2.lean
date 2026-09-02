import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL2
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
/-! Source kernel L2 = (1760, 100000, 540) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 1760 100000 540 = 62894479678030 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1760 100000 540 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 319475200 131071 100000 540 2438 = 16586280222373651167 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 319475200 131071 100000 540 2438 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 319475200 131071 100000 540 - 262144 * localRankBound 1760 100000 540 = 98869741656154847 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 319475200 131071 100000 540 2438 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL2
