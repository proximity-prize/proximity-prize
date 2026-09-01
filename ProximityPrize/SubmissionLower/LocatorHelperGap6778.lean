import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.N5

namespace ProximityPrize.SubmissionLower.LocatorHelperGap6778

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

theorem helper_rank :
    localRankBound 293 359728 87 = 1039941310584 := by
  rw [← LocatorKernelEval.localRankBound_eq 293 359728 87 (by decide)]
  decide

theorem helper_nullity :
    coefficientCount 53211437 131071 359728 87 -
      262144 * localRankBound 293 359728 87 = 1930116549504638 := by
  rw [helper_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    53211437 131071 359728 87 406 (by decide) (by decide)]
  decide

theorem finrank_lower_bound (u0 u1 : I → K) :
    1930116549504638 ≤ Module.finrank K
      (ConstraintKernel (K := K) 53211437 131071 359728 87 293
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    53211437 131071 359728 87 293 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact helper_nullity ▸ hlo'

end

end ProximityPrize.SubmissionLower.LocatorHelperGap6778
