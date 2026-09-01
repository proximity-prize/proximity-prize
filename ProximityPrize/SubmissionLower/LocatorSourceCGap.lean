import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorSourceCGap

open ProximityPrize.Benchmark
open LocatorArithmetic
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

theorem finrank_lower_bound (u0 u1 : I → K) :
    583914549944061 ≤ Module.finrank K
      (ConstraintKernel (K := K) 47947152 131071 149307 80 264
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    47947152 131071 149307 80 264 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact LocatorArithmetic.kernelC_nullity ▸ hlo'

end

end ProximityPrize.SubmissionLower.LocatorSourceCGap
