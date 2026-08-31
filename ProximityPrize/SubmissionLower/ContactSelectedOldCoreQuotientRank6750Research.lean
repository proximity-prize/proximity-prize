import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedCount6750Research
import ProximityPrize.SubmissionLower.ContactKernelCommonDivisorQuotientRank6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactSelectedOldCoreQuotientRank6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactRecursiveGCDResearch
open ContactStackedBoxTransport6656Research
open ContactTwoTailParameters6750Research
open ContactKernelCommonGCD6750Research
open ContactKernelCommonGCD6750Research.E80270
open ContactKernelCommonDivisorQuotientRank6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactSelectedCount6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

private theorem profileB_ys_cap_of_contact
    {x y r : Nat}
    (hc : x + 131071 * y + (131071 - 1) * r < 17096156) :
    y + r ≤ 130 := by
  omega

 


theorem profileB_flagBox_mem_nestedFiveCap (P : GlobalPoly)
    (hP : P ∈ ContactFlagInterpolation6641Research.globalCoefficientBox K
      17096156 131071 1708 29) :
    P ∈
      nestedFiveCapCoefficientBox K 17096156 131071 1708 130 29 := by
  intro d hd
  have h := hP hd
  rcases h with ⟨htotal, hslope, hcontact⟩
  exact ⟨htotal, profileB_ys_cap_of_contact hcontact,
    hslope, hcontact⟩

 
theorem oldCommonCore_ne_zero {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : oldCommonCore S ≠ 0 :=
  gcd123_ne_zero S.QA_ne_zero

 
def oldCoreQuotientLinear {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    BKernel u0 u1 →ₗ[K] GlobalPoly :=
  commonDivisorQuotientLinear 17096156 131071 1708 29 94
    IRSProfile.domain u0 u1 (oldCommonCore S) (oldCommonCore_ne_zero S)
      S.oldCore_dvd_B

theorem oldCoreQuotientLinear_injective {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    Function.Injective (oldCoreQuotientLinear S) := by
  exact commonDivisorQuotientLinear_injective
    17096156 131071 1708 29 94 IRSProfile.domain u0 u1
      (oldCommonCore S) (oldCommonCore_ne_zero S) S.oldCore_dvd_B

 

abbrev oldCoreQuotientBox {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : Submodule K GlobalPoly :=
  nestedFiveCapCoefficientBox K
    (17096156 - MvPolynomial.weightedTotalDegree
      (contactWeights 131071) (oldCommonCore S)) 131071
    (1708 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S)

theorem oldCoreQuotientLinear_mem_box {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) (z : BKernel u0 u1) :
    oldCoreQuotientLinear S z ∈ oldCoreQuotientBox S := by
  by_cases hz : z = 0
  · subst z
    rw [map_zero]
    exact (oldCoreQuotientBox S).zero_mem
  · have hq : oldCoreQuotientLinear S z ≠ 0 :=
      by
        simpa only [map_zero] using
          (oldCoreQuotientLinear_injective S).ne_iff.mpr hz
    have hmul : oldCommonCore S * oldCoreQuotientLinear S z =
        reconstruct K 17096156 131071 1708 29 z.1 := by
      exact mul_commonDivisorQuotientLinear
        17096156 131071 1708 29 94 IRSProfile.domain u0 u1
          (oldCommonCore S) (oldCommonCore_ne_zero S) S.oldCore_dvd_B z
    apply quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
      (oldCommonCore_ne_zero S) hq hmul
    · apply profileB_flagBox_mem_nestedFiveCap
      exact ContactFlagInterpolation6641Research.reconstruct_mem_globalCoefficientBox
        K 17096156 131071 1708 29 z.1
    · rfl
    · rfl
    · rfl
    · rfl

 
def oldCoreQuotientBoxLinear {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    BKernel u0 u1 →ₗ[K] oldCoreQuotientBox S :=
  LinearMap.codRestrict (oldCoreQuotientBox S)
    (oldCoreQuotientLinear S) (oldCoreQuotientLinear_mem_box S)

theorem oldCoreQuotientBoxLinear_injective {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    Function.Injective (oldCoreQuotientBoxLinear S) := by
  exact Function.Injective.codRestrict
    (oldCoreQuotientLinear_mem_box S) (oldCoreQuotientLinear_injective S)

 
theorem profileBKernel_finrank_lower (u0 u1 : I → K) :
    1382274190 ≤ Module.finrank K (BKernel u0 u1) := by
  have h := constraintKernel_finrank_lower_bound
    17096156 131071 1708 29 94 IRSProfile.domain u0 u1
  rw [show Fintype.card IRSProfile.Index = 262144 by
        norm_num [IRSProfile.Index],
    profileB_nullity_exact] at h
  exact h

 

theorem oldCoreQuotientBox_finrank_lower {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    1382274190 ≤ Module.finrank K (oldCoreQuotientBox S) := by
  letI : FiniteDimensional K (oldCoreQuotientBox S) :=
    nestedFiveCapCoefficientBox_finiteDimensional K _ _ _ _ _
  exact (profileBKernel_finrank_lower u0 u1).trans
    (LinearMap.finrank_le_finrank_of_injective
      (f := oldCoreQuotientBoxLinear S) (oldCoreQuotientBoxLinear_injective S))

end


end ContactSelectedOldCoreQuotientRank6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSelectedOldCoreQuotientRank6750Research.oldCoreQuotientBox_finrank_lower
