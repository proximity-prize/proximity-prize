import ProximityPrize.SubmissionLower.LocatorLargeSourceArithmetic6777

namespace ProximityPrize.SubmissionLower.LocatorSourceCLongGap

open ProximityPrize.Benchmark
open LocatorLargeSourceArithmetic6777
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

theorem finrank_lower_bound (u0 u1 : I → K) :
    1296392225018202 ≤ Module.finrank K
      (ConstraintKernel (K := K) helperWeighted 131071 helperLength
        helperSlope helperMultiplicity IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    helperWeighted 131071 helperLength helperSlope helperMultiplicity
      IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact helper_nullity_exact ▸ hlo'

end

end ProximityPrize.SubmissionLower.LocatorSourceCLongGap
