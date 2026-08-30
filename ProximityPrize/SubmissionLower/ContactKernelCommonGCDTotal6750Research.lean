import ProximityPrize.SubmissionLower.ContactKernelCommonGCDQuotientBox6750Research

namespace ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFactorCaps
open ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open Polynomial
open scoped Polynomial
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

universe w

namespace E80260

theorem profileB_commonGCD_total_le
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta IRSProfile.Field (BKernel u0 u1)) :
    wt residualTotalWeights (commonGCDAtMax (BKernel u0 u1) b) ≤ 1666 := by
  let V := BKernel u0 u1
  let H := commonGCDAtMax V b
  have hH : H ≠ 0 := commonGCDAtMax_ne_zero V b
  by_contra hnot
  change ¬ wt residualTotalWeights H ≤ 1666 at hnot
  have htotal : 1667 ≤ wt residualTotalWeights H := by omega
  have hqbox := commonQuotientLinear_mem_flagBox_of_total_lower
    17097096 131071 1668 29 94 1667 IRSProfile.domain u0 u1 b hH htotal
  have hobs := common_divisor_dimension_obstruction
    17097096 131071 1668 29 94 17097096 1 29
    IRSProfile.domain u0 u1 b hH hqbox
  rw [show Fintype.card IRSProfile.Index = 262144 by
    norm_num [IRSProfile.Index], profileB_nullity_exact,
    profileB_total_one_quotient_exact] at hobs
  omega

end E80260

end

end ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research
