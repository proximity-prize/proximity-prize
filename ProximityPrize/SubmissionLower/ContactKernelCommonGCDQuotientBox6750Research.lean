import ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research

 







namespace ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research

open scoped Classical BigOperators
open ContactFlagInterpolation6641Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFactorCaps
open ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

universe u v w

variable {K : Type u} [Field K]

 

theorem commonQuotientLinear_mem_flagBox_of_total_lower
    {I : Type v} [Fintype I]
    (D w0 L s m totalLower : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (htotal : totalLower ≤ wt residualTotalWeights
      (commonGCDAtMax
        (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b)) :
    ∀ z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1,
      commonQuotientLinear D w0 L s m nodes u0 u1 b hH z ∈
        globalCoefficientBox K D w0 (L - totalLower) s := by
  intro z
  by_cases hz : z = 0
  · subst z
    simpa only [map_zero] using
      (globalCoefficientBox K D w0 (L - totalLower) s).zero_mem
  · have hrecon :
        kernelReconstructLinear D w0 L s m nodes u0 u1 z ≠ 0 :=
      by
        simpa only [map_zero] using
          (kernelReconstructLinear_injective D w0 L s m nodes u0 u1).ne_iff.mpr hz
    let H := commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b
    let q := commonQuotientLinear D w0 L s m nodes u0 u1 b hH z
    have hq : q ≠ 0 := by
      intro hzero
      apply hrecon
      rw [← mul_commonQuotientLinear D w0 L s m nodes u0 u1 b hH z]
      simp [q, hzero]
    have hsource : kernelReconstructLinear D w0 L s m nodes u0 u1 z ∈
        globalCoefficientBox K D w0 L s := by
      rw [kernelReconstructLinear_apply]
      exact reconstruct_mem_globalCoefficientBox K D w0 L s z.1
    apply quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (kernelReconstructLinear D w0 L s m nodes u0 u1 z) H q
      D w0 L s 0 totalLower 0 hrecon hH hq hsource
    · exact (mul_commonQuotientLinear D w0 L s m nodes u0 u1 b hH z).symm
    · exact Nat.zero_le _
    · simpa only [H] using htotal
    · exact Nat.zero_le _

end

end ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research
