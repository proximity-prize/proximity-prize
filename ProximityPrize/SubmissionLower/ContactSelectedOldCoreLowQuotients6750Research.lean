import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedOldCoreQuotientRank6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientIntersection6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactSelectedOldCoreLowQuotients6750Research

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
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientIntersection6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreQuotientRank6750Research
open ContactKernelCommonDivisorQuotientRank6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

 
theorem oldCommonCore_contact_le {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) :
    MvPolynomial.weightedTotalDegree (contactWeights 131071)
        (oldCommonCore S) ≤ 8729951 := by
  have hdiv12 : gcd12 S.QA S.QB ∣ S.QA := gcd_dvd_left S.QA S.QB
  have hdiv123 : oldCommonCore S ∣ gcd12 S.QA S.QB :=
    gcd_dvd_left (gcd12 S.QA S.QB) S.QC
  have hdivA : oldCommonCore S ∣ S.QA := hdiv123.trans hdiv12
  have hcaps := (mem_flagGlobalCoefficientBox_iff S.QA
    8729952 131071 300000 14 (by norm_num)).mp S.QA_mem
  exact (weightedTotalDegree_le_of_dvd (contactWeights 131071)
    (oldCommonCore S) S.QA hdivA S.QA_ne_zero).trans hcaps.2.2

theorem oldCommonCore_total_le {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : oldCoreTotal S ≤ 1706 := by
  have hdiv : oldCommonCore S ∣ gcd12 S.QA S.QB :=
    gcd_dvd_left (gcd12 S.QA S.QB) S.QC
  have hne : gcd12 S.QA S.QB ≠ 0 := gcd12_ne_zero S.QA_ne_zero
  have hcaps := (mem_flagGlobalCoefficientBox_iff (gcd12 S.QA S.QB)
    8729952 131071 1706 14 (by norm_num)).mp S.gcd12_mem
  exact (weightedTotalDegree_le_of_dvd residualTotalWeights
    (oldCommonCore S) (gcd12 S.QA S.QB) hdiv hne).trans hcaps.1

theorem oldCommonCore_slope_le {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : oldCoreS S ≤ 14 := by
  have hdiv : oldCommonCore S ∣ gcd12 S.QA S.QB :=
    gcd_dvd_left (gcd12 S.QA S.QB) S.QC
  have hne : gcd12 S.QA S.QB ≠ 0 := gcd12_ne_zero S.QA_ne_zero
  have hcaps := (mem_flagGlobalCoefficientBox_iff (gcd12 S.QA S.QB)
    8729952 131071 1706 14 (by norm_num)).mp S.gcd12_mem
  exact (weightedTotalDegree_le_of_dvd residualSWeights
    (oldCommonCore S) (gcd12 S.QA S.QB) hdiv hne).trans hcaps.2.1

 

theorem oldCommonCore_ys_le {u0 u1 : I → K}
    (S : SelectedInterpolants6750 u0 u1) : oldCoreYS S ≤ 66 := by
  have hrel := residualYS_mul_le_contact_add_slope
    (oldCommonCore S) 131071 (by norm_num)
  have hc := oldCommonCore_contact_le S
  have hs := oldCommonCore_slope_le S
  change oldCoreYS S ≤ 66
  change 131071 * oldCoreYS S ≤
    MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (oldCommonCore S) + oldCoreS S at hrel
  omega

private theorem seedDegree_le_residualTotal (P : GlobalPoly) :
    MvPolynomial.weightedTotalDegree ContactFactorCaps.seedWeights P ≤
      MvPolynomial.weightedTotalDegree residualTotalWeights P := by
  apply (weightedTotalDegree_le_iff ContactFactorCaps.seedWeights P _).mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h ⊢
  simp [ContactFactorCaps.seedWeights, residualTotalWeights] at h ⊢
  omega

 
def derivativeParentCutoff (k : Nat) : Nat :=
  (94 - k) * 181874 + k * 131070

 



theorem exists_fixed_quotient_in_weighted_cutoff
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (targetD : Nat)
    (hD : targetD ≤ 17096156 -
      MvPolynomial.weightedTotalDegree (contactWeights 131071)
        (oldCommonCore S))
    (hgap : ((17096156 -
        MvPolynomial.weightedTotalDegree (contactWeights 131071)
          (oldCommonCore S)) - targetD) *
        nestedFiveCapChannelCount
          (1708 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S) <
      1382274190) :
    ∃ z : BKernel u0 u1,
      z ≠ 0 ∧ oldCoreQuotientLinear S z ≠ 0 ∧
      oldCommonCore S * oldCoreQuotientLinear S z =
        reconstruct K 17096156 131071 1708 29 z.1 ∧
      oldCoreQuotientLinear S z ∈
        nestedFiveCapCoefficientBox K targetD 131071
          (1708 - oldCoreTotal S) (130 - oldCoreYS S)
            (29 - oldCoreS S) := by
  let Dhigh := 17096156 -
    MvPolynomial.weightedTotalDegree (contactWeights 131071) (oldCommonCore S)
  let T := 1708 - oldCoreTotal S
  let YS := 130 - oldCoreYS S
  let R := 29 - oldCoreS S
  have himage : ∀ z : BKernel u0 u1,
      oldCoreQuotientLinear S z ∈
        nestedFiveCapCoefficientBox K Dhigh 131071 T YS R := by
    intro z
    simpa only [Dhigh, T, YS, R, oldCoreQuotientBox] using
      oldCoreQuotientLinear_mem_box S z
  have hsource : (Dhigh - targetD) * nestedFiveCapChannelCount T YS R <
      Module.finrank K (BKernel u0 u1) := by
    exact hgap.trans_le (profileBKernel_finrank_lower u0 u1)
  obtain ⟨z, hz, hQ, hQlow⟩ :=
    exists_nonzero_image_mem_low_nestedFiveCap K
      Dhigh targetD 131071 T YS R hD (oldCoreQuotientLinear S)
        himage (oldCoreQuotientLinear_injective S) hsource
  refine ⟨z, hz, hQ, ?_, ?_⟩
  · exact mul_commonDivisorQuotientLinear
      17096156 131071 1708 29 94 IRSProfile.domain u0 u1
        (oldCommonCore S) (oldCommonCore_ne_zero S) S.oldCore_dvd_B z
  · simpa only [T, YS, R] using hQlow

 





theorem exists_fixed_low_quotient
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (k : Nat) (hk : k ≤ 14)
    (hgap : k * 50804 * nestedFiveCapChannelCount
        (1708 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S) <
      1382274190) :
    ∃ z : BKernel u0 u1,
      z ≠ 0 ∧ oldCoreQuotientLinear S z ≠ 0 ∧
      oldCommonCore S * oldCoreQuotientLinear S z =
        reconstruct K 17096156 131071 1708 29 z.1 ∧
      oldCoreQuotientLinear S z ∈
        nestedFiveCapCoefficientBox K
          (derivativeParentCutoff k -
            MvPolynomial.weightedTotalDegree (contactWeights 131071)
              (oldCommonCore S))
          131071 (1708 - oldCoreTotal S) (130 - oldCoreYS S)
            (29 - oldCoreS S) := by
  let c := MvPolynomial.weightedTotalDegree (contactWeights 131071)
    (oldCommonCore S)
  let Dhigh := 17096156 - c
  let Dlow := derivativeParentCutoff k - c
  let T := 1708 - oldCoreTotal S
  let YS := 130 - oldCoreYS S
  let R := 29 - oldCoreS S
  have hc : c ≤ 8729951 := oldCommonCore_contact_le S
  have hcut : derivativeParentCutoff k = 17096156 - k * 50804 := by
    unfold derivativeParentCutoff
    omega
  have hcLow : c ≤ derivativeParentCutoff k := by
    rw [hcut]
    omega
  have hD : Dlow ≤ Dhigh := by
    dsimp [Dlow, Dhigh]
    omega
  have hwidth : Dhigh - Dlow = k * 50804 := by
    dsimp [Dhigh, Dlow]
    rw [hcut]
    omega
  have himage : ∀ z : BKernel u0 u1,
      oldCoreQuotientLinear S z ∈
        nestedFiveCapCoefficientBox K Dhigh 131071 T YS R := by
    intro z
    simpa only [Dhigh, T, YS, R, c, oldCoreQuotientBox] using
      oldCoreQuotientLinear_mem_box S z
  have hsource : (Dhigh - Dlow) * nestedFiveCapChannelCount T YS R <
      Module.finrank K (BKernel u0 u1) := by
    rw [hwidth]
    exact hgap.trans_le (profileBKernel_finrank_lower u0 u1)
  obtain ⟨z, hz, hQ, hQlow⟩ :=
    exists_nonzero_image_mem_low_nestedFiveCap K
      Dhigh Dlow 131071 T YS R hD (oldCoreQuotientLinear S)
        himage (oldCoreQuotientLinear_injective S) hsource
  refine ⟨z, hz, hQ, ?_, ?_⟩
  · exact mul_commonDivisorQuotientLinear
        17096156 131071 1708 29 94 IRSProfile.domain u0 u1
          (oldCommonCore S) (oldCommonCore_ne_zero S) S.oldCore_dvd_B z
  · simpa only [Dlow, T, YS, R, c] using hQlow

 



theorem exists_fixed_low_ordinary_quotient
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (k : Nat) (hk : k ≤ 14)
    (hgap : max
        (8729952 - MvPolynomial.weightedTotalDegree (contactWeights 131071)
          (oldCommonCore S))
        (k * 50804) * nestedFiveCapChannelCount
          (1708 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S) <
      1382274190) :
    ∃ z : BKernel u0 u1,
      z ≠ 0 ∧ oldCoreQuotientLinear S z ≠ 0 ∧
      oldCommonCore S * oldCoreQuotientLinear S z =
        reconstruct K 17096156 131071 1708 29 z.1 ∧
      oldCoreQuotientLinear S z ∈
        nestedFiveCapCoefficientBox K
          (min 8729952
            (derivativeParentCutoff k -
              MvPolynomial.weightedTotalDegree (contactWeights 131071)
                (oldCommonCore S)))
          131071 (1708 - oldCoreTotal S) (130 - oldCoreYS S)
            (29 - oldCoreS S) := by
  let c := MvPolynomial.weightedTotalDegree (contactWeights 131071)
    (oldCommonCore S)
  let Dhigh := 17096156 - c
  let Dderiv := derivativeParentCutoff k - c
  let targetD := min 8729952 Dderiv
  let channels := nestedFiveCapChannelCount
    (1708 - oldCoreTotal S) (130 - oldCoreYS S) (29 - oldCoreS S)
  have hc : c ≤ 8729951 := oldCommonCore_contact_le S
  have hcut : derivativeParentCutoff k = 17096156 - k * 50804 := by
    unfold derivativeParentCutoff
    omega
  have hcLow : c ≤ derivativeParentCutoff k := by
    rw [hcut]
    omega
  have hderiv : Dderiv ≤ Dhigh := by
    dsimp [Dderiv, Dhigh]
    omega
  have htarget : targetD ≤ Dhigh :=
    (min_le_right 8729952 Dderiv).trans hderiv
  have hwidth : Dhigh - targetD ≤ max (8729952 - c) (k * 50804) := by
    by_cases hle : 8729952 ≤ Dderiv
    · have heq : targetD = 8729952 := min_eq_left hle
      rw [heq]
      have hw : Dhigh - 8729952 ≤ 8729952 - c := by
        dsimp [Dhigh]
        omega
      exact hw.trans (le_max_left _ _)
    · have hrev : Dderiv ≤ 8729952 := Nat.le_of_not_ge hle
      have heq : targetD = Dderiv := min_eq_right hrev
      rw [heq]
      have hw : Dhigh - Dderiv = k * 50804 := by
        dsimp [Dhigh, Dderiv]
        rw [hcut]
        omega
      rw [hw]
      exact le_max_right _ _
  have hgap' : (Dhigh - targetD) * channels < 1382274190 :=
    (Nat.mul_le_mul_right channels hwidth).trans_lt hgap
  simpa only [targetD, Dderiv, Dhigh, channels, c] using
    exists_fixed_quotient_in_weighted_cutoff S targetD htarget hgap'

 



theorem reconstruct_mem_derivative_box_of_fixed_low_quotient
    {u0 u1 : I → K} (S : SelectedInterpolants6750 u0 u1)
    (j : Nat) (hj : j ≤ 14) (z : BKernel u0 u1) (hz : z ≠ 0)
    (hQlow : oldCoreQuotientLinear S z ∈
      nestedFiveCapCoefficientBox K
        (derivativeParentCutoff j -
          MvPolynomial.weightedTotalDegree (contactWeights 131071)
            (oldCommonCore S))
        131071 (1708 - oldCoreTotal S) (130 - oldCoreYS S)
          (29 - oldCoreS S))
    (k : Nat) (hkj : k ≤ j) :
    reconstruct K 17096156 131071 1708 29 z.1 ∈
      ContactInterpolation.globalCoefficientBox K
        (derivativeParentCutoff k) 131071 1708 29 := by
  let G := oldCommonCore S
  let Q := oldCoreQuotientLinear S z
  let c := MvPolynomial.weightedTotalDegree (contactWeights 131071) G
  let targetD := derivativeParentCutoff j - c
  have hG : G ≠ 0 := oldCommonCore_ne_zero S
  have hQ : Q ≠ 0 := by
    have h := (oldCoreQuotientLinear_injective S).ne_iff.mpr hz
    simpa only [Q, map_zero] using h
  have hc : c ≤ 8729951 := oldCommonCore_contact_le S
  have hjcut : derivativeParentCutoff j = 17096156 - j * 50804 := by
    unfold derivativeParentCutoff
    omega
  have hkcut : derivativeParentCutoff k = 17096156 - k * 50804 := by
    unfold derivativeParentCutoff
    omega
  have hcj : c ≤ derivativeParentCutoff j := by
    rw [hjcut]
    omega
  have htarget : 0 < targetD := by
    dsimp [targetD]
    rw [hjcut]
    omega
  have hcutmono : derivativeParentCutoff j ≤ derivativeParentCutoff k := by
    rw [hjcut, hkcut]
    omega
  have hQcaps :=
    (mem_nestedFiveCapCoefficientBox_iff Q targetD 131071
        (1708 - oldCoreTotal S) (130 - oldCoreYS S)
          (29 - oldCoreS S) htarget).mp (by
            simpa only [Q, targetD, G, c] using hQlow)
  have hmul : G * Q = reconstruct K 17096156 131071 1708 29 z.1 := by
    exact mul_commonDivisorQuotientLinear
      17096156 131071 1708 29 94 IRSProfile.domain u0 u1
        G hG S.oldCore_dvd_B z
  have htotalCore : oldCoreTotal S ≤ 1706 := oldCommonCore_total_le S
  have hslopeCore : oldCoreS S ≤ 14 := oldCommonCore_slope_le S
  have htotal : MvPolynomial.weightedTotalDegree residualTotalWeights
      (reconstruct K 17096156 131071 1708 29 z.1) ≤ 1708 := by
    rw [← hmul, weightedTotalDegree_mul residualTotalWeights G Q hG hQ]
    change oldCoreTotal S +
      MvPolynomial.weightedTotalDegree residualTotalWeights Q ≤ 1708
    omega
  have hslope : MvPolynomial.weightedTotalDegree
      ContactFactorCaps.slopeWeights
      (reconstruct K 17096156 131071 1708 29 z.1) ≤ 29 := by
    have hs : MvPolynomial.weightedTotalDegree residualSWeights
        (reconstruct K 17096156 131071 1708 29 z.1) ≤ 29 := by
      rw [← hmul, weightedTotalDegree_mul residualSWeights G Q hG hQ]
      change oldCoreS S +
        MvPolynomial.weightedTotalDegree residualSWeights Q ≤ 29
      omega
    simpa only [ContactFactorCaps.slopeWeights, residualSWeights] using hs
  have hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071)
      (reconstruct K 17096156 131071 1708 29 z.1) ≤
        derivativeParentCutoff k - 1 := by
    rw [← hmul, weightedTotalDegree_mul (contactWeights 131071) G Q hG hQ]
    change c + MvPolynomial.weightedTotalDegree
      (contactWeights 131071) Q ≤ derivativeParentCutoff k - 1
    have htargLe : targetD ≤ derivativeParentCutoff j - c := le_rfl
    omega
  have hseed : MvPolynomial.weightedTotalDegree ContactFactorCaps.seedWeights
      (reconstruct K 17096156 131071 1708 29 z.1) ≤ 1708 :=
    (seedDegree_le_residualTotal _).trans htotal
  apply (ContactFactorCaps.mem_globalCoefficientBox_iff
    (reconstruct K 17096156 131071 1708 29 z.1)
      (derivativeParentCutoff k) 131071 1708 29 (by
        rw [hkcut]
        omega)).mpr
  exact ⟨hseed, hslope, hcontact⟩

end

end ContactSelectedOldCoreLowQuotients6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSelectedOldCoreLowQuotients6750Research.exists_fixed_low_quotient
