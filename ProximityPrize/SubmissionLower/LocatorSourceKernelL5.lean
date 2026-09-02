import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelL5
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel L5 = (3120, 200000, 960) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 3120 200000 960 = 702078387192640 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 3120 200000 960 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 566342400 131071 200000 960 4321 = 185219554273546005040 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 566342400 131071 200000 960 4321 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 566342400 131071 200000 960 - 262144 * localRankBound 3120 200000 960 = 1173917541318584880 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 566342400 131071 200000 960 4321 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelL5
