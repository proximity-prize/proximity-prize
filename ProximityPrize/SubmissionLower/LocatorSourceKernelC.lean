import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelC
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel C = (400, 130000, 120) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 400 130000 120 = 958541142020 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 400 130000 120 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 72608000 131071 130000 120 554 = 252867394627334058 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 72608000 131071 130000 120 554 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 72608000 131071 130000 120 - 262144 * localRankBound 400 130000 120 = 1591585493643178 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 72608000 131071 130000 120 554 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelC
