import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelN4
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel N4 = (5200, 400000, 1600) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 5200 400000 1600 = 6504399142910400 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 5200 400000 1600 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 943904000 131071 400000 1600 7202 = 1716589278768329959600 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 943904000 131071 400000 1600 7202 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 943904000 131071 400000 1600 - 262144 * localRankBound 5200 400000 1600 = 11500069849226062000 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 943904000 131071 400000 1600 7202 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelN4
