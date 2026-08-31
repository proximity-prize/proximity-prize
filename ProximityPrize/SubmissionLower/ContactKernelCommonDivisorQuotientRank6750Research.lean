import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactKernelCommonDivisorQuotientRank6750Research

open scoped Classical
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactKernelCommonGCD6750Research
open ContactFixedFactorQuotientLinear6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 


def commonDivisorQuotientLinear
    {I : Type v} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K)
    (G : Poly4 K) (hG : G ≠ 0)
    (hdiv : ∀ z : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      G ∣ reconstruct K D w L s z.1) :
    ConstraintKernel (K := K) D w L s m nodes u0 u1 →ₗ[K] Poly4 K :=
  mappedFixedFactorQuotientLinearMap G hG
    (kernelReconstructLinear D w L s m nodes u0 u1) (by
      intro z
      simpa only [kernelReconstructLinear_apply] using hdiv z)

 
theorem mul_commonDivisorQuotientLinear
    {I : Type v} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K)
    (G : Poly4 K) (hG : G ≠ 0)
    (hdiv : ∀ z : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      G ∣ reconstruct K D w L s z.1)
    (z : ConstraintKernel (K := K) D w L s m nodes u0 u1) :
    G * commonDivisorQuotientLinear D w L s m nodes u0 u1 G hG hdiv z =
      reconstruct K D w L s z.1 := by
  exact mul_mappedFixedFactorQuotientLinearMap G hG
    (kernelReconstructLinear D w L s m nodes u0 u1) (by
      intro v
      simpa only [kernelReconstructLinear_apply] using hdiv v) z

theorem commonDivisorQuotientLinear_injective
    {I : Type v} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K)
    (G : Poly4 K) (hG : G ≠ 0)
    (hdiv : ∀ z : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      G ∣ reconstruct K D w L s z.1) :
    Function.Injective
      (commonDivisorQuotientLinear D w L s m nodes u0 u1 G hG hdiv) := by
  apply mappedFixedFactorQuotientLinearMap_injective
  exact kernelReconstructLinear_injective D w L s m nodes u0 u1

 



theorem constraintKernel_finrank_le_of_commonDivisor_quotients_mem
    {I : Type v} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K)
    (G : Poly4 K) (hG : G ≠ 0)
    (hdiv : ∀ z : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      G ∣ reconstruct K D w L s z.1)
    (W : Submodule K (Poly4 K)) [Module.Finite K W]
    (hmem : ∀ z, commonDivisorQuotientLinear
      D w L s m nodes u0 u1 G hG hdiv z ∈ W) :
    Module.finrank K
        (ConstraintKernel (K := K) D w L s m nodes u0 u1) ≤
      Module.finrank K W := by
  let q : ConstraintKernel (K := K) D w L s m nodes u0 u1 →ₗ[K] W :=
    LinearMap.codRestrict W
      (commonDivisorQuotientLinear D w L s m nodes u0 u1 G hG hdiv) hmem
  apply LinearMap.finrank_le_finrank_of_injective (f := q)
  intro x y hxy
  apply commonDivisorQuotientLinear_injective
    D w L s m nodes u0 u1 G hG hdiv
  exact congrArg Subtype.val hxy

 


theorem exists_commonDivisor_quotient_not_mem_of_finrank_lt
    {I : Type v} [Fintype I]
    (D w L s m : Nat) (nodes u0 u1 : I → K)
    (G : Poly4 K) (hG : G ≠ 0)
    (hdiv : ∀ z : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      G ∣ reconstruct K D w L s z.1)
    (W : Submodule K (Poly4 K)) [Module.Finite K W]
    (hsmall : Module.finrank K W <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s) :
    ∃ z, commonDivisorQuotientLinear
      D w L s m nodes u0 u1 G hG hdiv z ∉ W := by
  by_contra hall
  push_neg at hall
  have hle := constraintKernel_finrank_le_of_commonDivisor_quotients_mem
    D w L s m nodes u0 u1 G hG hdiv W hall
  have hlower := constraintKernel_finrank_lower_bound
    D w L s m nodes u0 u1
  omega

end


end ContactKernelCommonDivisorQuotientRank6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactKernelCommonDivisorQuotientRank6750Research.commonDivisorQuotientLinear_injective
#print axioms ProximityPrize.SubmissionLower.ContactKernelCommonDivisorQuotientRank6750Research.constraintKernel_finrank_le_of_commonDivisor_quotients_mem
#print axioms ProximityPrize.SubmissionLower.ContactKernelCommonDivisorQuotientRank6750Research.exists_commonDivisor_quotient_not_mem_of_finrank_lt
