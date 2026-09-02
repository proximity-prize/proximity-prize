import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRowClosed
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelAux
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel Aux = (76, 130000, 23) at agreements 181520: rank through the closed form of
`LocatorRankClosed`, nullity through the row closed form of `LocatorRowClosed`. -/
theorem rank_eq : localRankBound 76 130000 23 = 6962613720 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 76 130000 23 (by decide)]
  decide +kernel
theorem cutoff_eq : LocatorKernelEval.coefficientCountCutoff 13795520 131071 130000 23 106 = 1825629832836026 := by
  rw [LocatorRowClosed.cutoff_eq_rowsClosed 13795520 131071 130000 23 106 (by decide)
    (by intro i hi; omega) (by intro i hi; omega)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 13795520 131071 130000 23 - 262144 * localRankBound 76 130000 23 = 422421820346 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 13795520 131071 130000 23 106 (by decide) (by decide), cutoff_eq]
end ProximityPrize.SubmissionLower.LocatorSourceKernelAux
