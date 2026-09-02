import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
namespace ProximityPrize.SubmissionLower.LocatorSourceKernelT15k
open ProximityPrize.Benchmark RCN100 RCN119
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000
set_option Elab.async false
/-! Source kernel T15k = (550, 15000, 170) at agreements 181520: rank and nullity. -/
theorem rank_eq : localRankBound 550 15000 170 = 288730354170 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 550 15000 170 (by decide)]
  decide +kernel
theorem nullity_eq :
    coefficientCount 99836000 131071 15000 170 - 262144 * localRankBound 550 15000 170 = 236413037510670 := by
  rw [rank_eq, LocatorKernelEval.coefficientCount_eq_cutoff 99836000 131071 15000 170 762 (by decide) (by decide)]
  decide +kernel
end ProximityPrize.SubmissionLower.LocatorSourceKernelT15k
