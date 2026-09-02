import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelN3
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel N3 = (4600, 400000, 1400) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 4600 400000 1400 = 4469050310913300 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 4600 400000 1400 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 834992000 131071 400000 1400 6371 = 1179572900911814982860 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 834992000 131071 400000 1400 6371 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 834992000 131071 400000 1400 - 262144 * localRankBound 4600 400000 1400 = 8038176207758867660 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 834992000 131071 400000 1400 6371 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelN3
