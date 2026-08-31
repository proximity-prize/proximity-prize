import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualFullBoxAdapter6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactCanonicalHighSourceThirdNonzero6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open UniqueFactorizationMonoid
open ContactTranslation
open ContactPrimeSeedIncidence
open ContactProperCutSeedCount
open ContactFlagInterpolation6641Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactFactorCaps
open ContactFullKernelCoprimePair6660Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighSourceAssembly6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactAnchoredThirdResidual6750Research
open ContactAnchoredThirdResidualAdapter6750Research
open ContactAnchoredThirdResidualFullBoxAdapter6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research
open ContactResidualContactDegree6750Research
open ContactIdentityResidualGlobalFlagResearch
open ContactFlagNestedCommonCoreRealizer6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

theorem commonCoreNonzeroSeeds_card_le_of_canonicalHighSource_full_box
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (commonCoreNonzeroSeeds
      (canonicalHighSourceCore IRSProfile.domain u0 u1 g)
      selected Gamma).card ≤
      (thirdStage (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g)).regularCountCap +
      (thirdPivot (canonicalCoreTotal u0 u1 g)
        (canonicalCoreS u0 u1 g)).countCap := by
  let H := canonicalHighSourceCore IRSProfile.domain u0 u1 g
  let V := highSourceHull IRSProfile.domain u0 u1 g
  let c := canonicalCoreContact u0 u1 g
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  have hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H = c :=
    rfl
  have hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights H = t :=
    rfl
  have hHys : MvPolynomial.weightedTotalDegree residualYSWeights H = y :=
    rfl
  have hHs : MvPolynomial.weightedTotalDegree residualSWeights H = r :=
    rfl
  have hH : H ≠ 0 :=
    canonicalHighSourceCore_ne_zero_of_fixed
      IRSProfile.domain u0 u1 g source.source_ne_zero
  have hHdiv : H ∣ reconstruct K 11458062 131071 familyMaxTotal 18 g :=
    canonicalHighSourceCore_dvd_fixed_reconstruct IRSProfile.domain u0 u1 g
  have hsourceCaps :=
    (mem_nestedFiveCapCoefficientBox_iff
      (reconstruct K 11458062 131071 familyMaxTotal 18 g)
      (48 * ContactAnchoredOneFamilySelector6750Research.agreements)
      131071 1706 66 14 (by
        norm_num [ContactAnchoredOneFamilySelector6750Research.agreements])).mp
      source.source_mem_fiveCap
  have ht : t ≤ 1706 := by
    rw [← hHtotal]
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights H
      (reconstruct K 11458062 131071 familyMaxTotal 18 g)
      hHdiv source.source_ne_zero).trans hsourceCaps.1
  have hy : y ≤ 66 := by
    rw [← hHys]
    exact (weightedTotalDegree_le_of_dvd residualYSWeights H
      (reconstruct K 11458062 131071 familyMaxTotal 18 g)
      hHdiv source.source_ne_zero).trans hsourceCaps.2.1
  have hr : r ≤ 14 := by
    rw [← hHs]
    exact (weightedTotalDegree_le_of_dvd residualSWeights H
      (reconstruct K 11458062 131071 familyMaxTotal 18 g)
      hHdiv source.source_ne_zero).trans hsourceCaps.2.2.1
  have hcardI : Fintype.card I = domainSize := by
    norm_num [I, IRSProfile.Index, domainSize]
  have hgV : g ∈ V := by
    exact fixed_mem_adjoinFixedArray g
      (fullHighKernelFamilySum IRSProfile.domain u0 u1)
  have hfinite : ∀ Q : Poly4,
      reconstruct K 11458062 131071 familyMaxTotal 18 g = H * Q →
      Q ≠ 0 → (allFactors Q).card < ENat.card K := by
    intro Q hfactor hQ
    have hQfive : Q ∈ nestedFiveCapCoefficientBox K
        (48 * ContactAnchoredOneFamilySelector6750Research.agreements - c)
        131071 (1706 - t) (66 - y) (14 - r) := by
      exact quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
        hH hQ hfactor.symm source.source_mem_fiveCap
        hHcontact hHtotal hHys hHs
    have hQbox : Q ∈ ContactInterpolation.globalCoefficientBox K
        (thirdPivot t r).D (thirdPivot t r).w
        (thirdPivot t r).L (thirdPivot t r).s := by
      simpa only [K, Poly4,
          ContactAnchoredThirdResidualAdapter6750Research.K,
          ContactAnchoredThirdResidualAdapter6750Research.Poly4] using
        (fiveCap_mem_thirdPivot_box (Q := Q) (t := t) (r := r)
          (D := 48 * ContactAnchoredThirdResidual6750Research.agreements - c)
          (T := 1706 - t) (YS := 66 - y) (S := 14 - r)
          (Nat.sub_le _ _) (by omega) (by omega) (by
            simpa only [K,
              ContactAnchoredThirdResidualAdapter6750Research.K,
              ContactAnchoredThirdResidualAdapter6750Research.Poly4, w,
              ContactAnchoredThirdResidual6750Research.agreements,
              ContactAnchoredOneFamilySelector6750Research.agreements] using
              hQfive))
    exact highSource_thirdPivot_allFactors_card_lt_field hQ hQbox
  obtain ⟨Q, hQ, hQfactorRaw, vT, hvTfamily, T, hTfactorRaw, hcoprime⟩ :=
    exists_coprime_commonGCDAtMax_residual
      11458062 131071 familyMaxTotal 18 63 IRSProfile.domain u0 u1
      highFamilyCap highFamilyCap_le
      (fullHighKernelSelection IRSProfile.domain u0 u1) g
      (highSourceBasis IRSProfile.domain u0 u1 g) source.source_ne_zero (by
        intro Q hfactor hQ
        apply hfinite Q
        · simpa only [H, canonicalHighSourceCore, highSourceCore,
            highSourceHull, fullHighKernelFamilySum] using hfactor
        · exact hQ)
  have hQfactor :
      reconstruct K 11458062 131071 familyMaxTotal 18 g = H * Q := by
    simpa only [H, canonicalHighSourceCore, highSourceCore,
      highSourceHull, fullHighKernelFamilySum] using hQfactorRaw
  have hTfactor :
      reconstruct K 11458062 131071 familyMaxTotal 18 vT.1 = H * T := by
    simpa only [H, canonicalHighSourceCore, highSourceCore,
      highSourceHull, fullHighKernelFamilySum] using hTfactorRaw
  have hQfive : Q ∈ nestedFiveCapCoefficientBox K
      (48 * ContactAnchoredOneFamilySelector6750Research.agreements - c)
      131071 (1706 - t) (66 - y) (14 - r) := by
    exact quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
      hH hQ hQfactor.symm source.source_mem_fiveCap
      hHcontact hHtotal hHys hHs
  have hTparent :
      reconstruct K 11458062 131071 familyMaxTotal 18 vT.1 ∈
        nestedFiveCapCoefficientBox K 11458062 131071
          familyMaxTotal familyYSCap familySlopeCap := by
    let a : fullHighKernelFamilySum IRSProfile.domain u0 u1 :=
      ⟨vT.1, by simpa only [fullHighKernelFamilySum] using hvTfamily⟩
    have ha := reconstruct_mem_high_parent_of_mem_fullHighKernelFamilySum
      IRSProfile.domain u0 u1 a
    simpa only [a, K, familyYSCap, familySlopeCap] using ha
  have hTfive : T ∈ nestedFiveCapCoefficientBox K
      (11458062 - c) 131071
      (familyMaxTotal - t) (familyYSCap - y) (familySlopeCap - r) := by
    by_cases hT : T = 0
    · subst T
      exact Submodule.zero_mem _
    · exact quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
        hH hT hTfactor.symm hTparent hHcontact hHtotal hHys hHs
  have hrel : IsRelPrime Q T := by
    intro C hCQ hCT
    exact hcoprime C hCQ hCT
  have hcontactLower : 131071 * y - r ≤ c := by
    rw [← hHcontact, ← hHys, ← hHs]
    exact residualYS_mul_sub_residualS_le_contact 131071 (by norm_num) H hH
  have hrightContact :
      11458062 - c ≤
        63 * ContactAnchoredThirdResidual6750Research.agreements -
          (w * (y - 1) - r) := by
    norm_num [ContactAnchoredThirdResidual6750Research.agreements, w] at *
    omega
  have hdegree : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    simpa only [w] using semantics.selected_degree gamma
      (commonCoreNonzeroSeeds_subset H selected Gamma hgamma)
  have hagreement : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      ContactAnchoredThirdResidual6750Research.agreements ≤
        ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    have hgammaGamma := commonCoreNonzeroSeeds_subset H selected Gamma hgamma
    have hsub : semantics.support gamma ⊆
        (Finset.univ : Finset I).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact semantics.agreement_values gamma hgammaGamma i hi
    exact (semantics.agreement_card gamma hgammaGamma).trans
      (Finset.card_le_card hsub)
  have hcancel : ∀ gamma ∈ commonCoreNonzeroSeeds H selected Gamma,
      ∀ v : V, ∀ R : Poly4,
      reconstruct K 11458062 131071 familyMaxTotal 18 v.1 = H * R →
        specialization K (selected gamma) gamma R = 0 := by
    intro gamma hgamma v R hfactor
    have hgammaGamma := commonCoreNonzeroSeeds_subset H selected Gamma hgamma
    have hcore : specialization K (selected gamma) gamma H ≠ 0 :=
      (Finset.mem_filter.mp hgamma).2
    exact highSourceHull_quotient_specializes_zero
      IRSProfile.domain u0 u1 g
      (highSourceBasis IRSProfile.domain u0 u1 g)
      (selected gamma) gamma (semantics.support gamma)
      (semantics.selected_degree gamma hgammaGamma)
      (semantics.agreement_card gamma hgammaGamma)
      (semantics.agreement_values gamma hgammaGamma)
      (source.source_vanishes gamma hgammaGamma) hcore v R hfactor
  have residualCount : ResidualCountProvider V g H selected Gamma
      1706 66 14
      ((thirdStage t y r).regularCountCap + (thirdPivot t r).countCap) := by
    apply residualCountProvider_of_third_residual_full_old_core
      V g H Q T selected Gamma 1706 66 14 t y r ht hy hr
      vT hQ hrel hQfactor hTfactor hQfive
    · simpa only [ContactAnchoredThirdResidual6750Research.agreements,
          ContactAnchoredOneFamilySelector6750Research.agreements] using
        (Nat.sub_le
          (48 * ContactAnchoredOneFamilySelector6750Research.agreements) c)
    · omega
    · omega
    · exact hTfive
    · exact hrightContact
    · exact Nat.sub_le_sub_right (by norm_num [familyMaxTotal]) t
    · exact Nat.sub_le_sub_right (by norm_num [familySlopeCap]) r
    · exact hdegree
    · exact hagreement
    · exact noLargeSelectedPencil_mono selected Gamma
        (commonCoreNonzeroSeeds H selected Gamma) w errors
        (commonCoreNonzeroSeeds_subset H selected Gamma) hnoPencil
  have hsourceHigh :
      reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
        nestedFiveCapCoefficientBox K 11458062 131071 1706 66 14 := by
    apply nestedFiveCapCoefficientBox_mono_D
      (F := K) (Dlow :=
        48 * ContactAnchoredOneFamilySelector6750Research.agreements)
    · norm_num [ContactAnchoredOneFamilySelector6750Research.agreements]
    · exact source.source_mem_fiveCap
  exact residualCount source.source_ne_zero hsourceHigh hgV hcancel

end

end ContactCanonicalHighSourceThirdNonzero6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceThirdNonzero6750Research.commonCoreNonzeroSeeds_card_le_of_canonicalHighSource_full_box
