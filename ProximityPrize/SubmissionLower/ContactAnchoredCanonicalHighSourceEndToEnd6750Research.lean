import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHighSourceAssembly6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidualAdapter6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedCommonCoreRealizer6750Research
import ProximityPrize.SubmissionLower.ContactFullKernelCoprimePair6660Research
import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactCanonicalHighSourceUniformThirdCap6750Research

 












namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredCanonicalHighSourceEndToEnd6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open UniqueFactorizationMonoid
open ContactTranslation
open ContactPrimeSeedIncidence
open ContactFlagInterpolation6641Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactFactorCaps
open ContactFullKernelCoprimePair6660Research
open ContactFullKernelHeightTwoRouting6660Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighSourceAssembly6750Research
open ContactAnchoredThirdResidual6750Research
open ContactAnchoredThirdResidualAdapter6750Research
open ContactFlagNestedCommonCoreRealizer6750Research
open ContactResidualContactDegree6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 300000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

 

def canonicalCoreContact
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) : Nat :=
  MvPolynomial.weightedTotalDegree (contactWeights 131071)
    (canonicalHighSourceCore IRSProfile.domain u0 u1 g)

def canonicalCoreTotal
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) : Nat :=
  MvPolynomial.weightedTotalDegree
    ContactIdentityResidualGlobalFlagResearch.residualTotalWeights
    (canonicalHighSourceCore IRSProfile.domain u0 u1 g)

def canonicalCoreYS
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) : Nat :=
  MvPolynomial.weightedTotalDegree
    ContactIdentityResidualGlobalFlagResearch.residualYSWeights
    (canonicalHighSourceCore IRSProfile.domain u0 u1 g)

def canonicalCoreS
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) : Nat :=
  MvPolynomial.weightedTotalDegree
    ContactIdentityResidualGlobalFlagResearch.residualSWeights
    (canonicalHighSourceCore IRSProfile.domain u0 u1 g)

 


abbrev CanonicalHighSourceStageBound
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K) (cap : Nat) : Prop :=
  ∀
    (theta : LinearMap.ker
      (constraintMap K 11458062 131071
        (selectedTotal (canonicalCoreTotal u0 u1 g)
          (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
        18 63 IRSProfile.domain u0 u1))
    (Q : Poly4),
    theta ≠ 0 → Q ≠ 0 →
    canonicalHighSourceCore IRSProfile.domain u0 u1 g * Q =
      reconstruct K 11458062 131071
        (selectedTotal (canonicalCoreTotal u0 u1 g)
          (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
        18 theta.1 →
    Q ∈ nestedFiveCapCoefficientBox K
      (11407258 - canonicalCoreContact u0 u1 g) 131071
      (selectedTotal (canonicalCoreTotal u0 u1 g)
          (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g) -
        canonicalCoreTotal u0 u1 g)
      (familyYSCap - canonicalCoreYS u0 u1 g)
      (familySlopeCap - canonicalCoreS u0 u1 g) →
    ∃ C : AnchoredStageCertificate
        (canonicalHighSourceCore IRSProfile.domain u0 u1 g) Q selected
        (commonCoreZeroSeeds
          (canonicalHighSourceCore IRSProfile.domain u0 u1 g)
          selected Gamma),
      C.cost ≤ cap

 

structure FixedHighSourceCertificate
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K) where
  source_ne_zero :
    reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0
  source_mem_fiveCap :
    reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
      nestedFiveCapCoefficientBox K
        (48 * ContactAnchoredOneFamilySelector6750Research.agreements)
        131071 1706 66 14
  source_vanishes : ∀ gamma ∈ Gamma,
    specialization K (selected gamma) gamma
      (reconstruct K 11458062 131071 familyMaxTotal 18 g) = 0

 

theorem HardCell.r_ge_8_for_third
    {t y r : Nat} (cell : HardCell t y r) : 8 ≤ r := by
  apply (show 8 ≤ hostileMinR y from ?_).trans cell.r_lower
  unfold hostileMinR
  split_ifs <;> omega

theorem HardCell.t_ge_897_for_third
    {t y r : Nat} (cell : HardCell t y r) : 886 ≤ t := by
  have hcheck : ∀ (yy : Fin 67), 38 ≤ yy.val →
      ∀ rr : Fin 15, hostileMinR yy.val ≤ rr.val →
        886 ≤ hardMinT yy.val rr.val := by
    decide
  have hmin : 886 ≤ hardMinT y r :=
    hcheck ⟨y, Nat.lt_succ_iff.mpr cell.y_upper⟩ cell.y_lower
      ⟨r, Nat.lt_succ_iff.mpr cell.r_upper⟩ cell.r_lower
  exact hmin.trans cell.t_lower

 

theorem highSource_thirdPivot_allFactors_card_lt_field
    {Q : Poly4} {t r : Nat} (hQ : Q ≠ 0)
    (hbox : Q ∈ ContactInterpolation.globalCoefficientBox K
      (thirdPivot t r).D (thirdPivot t r).w
      (thirdPivot t r).L (thirdPivot t r).s) :
    (allFactors Q).card < ENat.card K := by
  have hx : Q.degreeOf (0 : Fin 4) ≤ (thirdPivot t r).D - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have hweighted := (hbox hd).2.2
    omega
  have hcaps := ContactFactorCaps.degree_bounds_of_mem_box Q
    (thirdPivot t r).D (thirdPivot t r).w
    (thirdPivot t r).L (thirdPivot t r).s
    (by norm_num [thirdPivot, w]) hbox
  have hy := hcaps.1
  have hr := hcaps.2.1
  have hz := hcaps.2.2
  have hall := allFactors_card_le_coordinate_degree_sum Q hQ
  simp only [Fin.sum_univ_four] at hall
  have hcoarse : (allFactors Q).card ≤ 8731739 := by
    simp only [thirdPivot,
      ContactAnchoredThirdResidual6750Research.agreements, w] at hx hy hr hz
    omega
  rw [ENat.card_eq_coe_fintype_card,
    AlignmentProtocol6401Conditional.field_cardinality]
  exact_mod_cast hcoarse.trans_lt (by norm_num)

 

 





theorem fixedSeeds_card_le_of_canonicalHighSource
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (anchoredCap : Nat)
    (stageBound : ∀
      (theta : LinearMap.ker
        (constraintMap K 11458062 131071
          (selectedTotal (canonicalCoreTotal u0 u1 g)
            (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
          18 63 IRSProfile.domain u0 u1))
      (Q : Poly4),
      theta ≠ 0 → Q ≠ 0 →
      canonicalHighSourceCore IRSProfile.domain u0 u1 g * Q =
        reconstruct K 11458062 131071
          (selectedTotal (canonicalCoreTotal u0 u1 g)
            (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
          18 theta.1 →
      Q ∈ nestedFiveCapCoefficientBox K
        (11407258 - canonicalCoreContact u0 u1 g) 131071
        (selectedTotal (canonicalCoreTotal u0 u1 g)
            (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g) -
          canonicalCoreTotal u0 u1 g)
        (familyYSCap - canonicalCoreYS u0 u1 g)
        (familySlopeCap - canonicalCoreS u0 u1 g) →
      ∃ C : AnchoredStageCertificate
          (canonicalHighSourceCore IRSProfile.domain u0 u1 g) Q selected
          (commonCoreZeroSeeds
            (canonicalHighSourceCore IRSProfile.domain u0 u1 g)
            selected Gamma),
        C.cost ≤ anchoredCap)
    (hnoPencil : NoLargeSelectedPencil selected
      (commonCoreNonzeroSeeds
        (canonicalHighSourceCore IRSProfile.domain u0 u1 g)
        selected Gamma) w errors) :
    Gamma.card ≤ anchoredCap +
      ((thirdStage (canonicalCoreTotal u0 u1 g)
          (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g)).regularCountCap +
        (thirdPivot (canonicalCoreTotal u0 u1 g)
          (canonicalCoreS u0 u1 g)).countCap) := by
  let H := canonicalHighSourceCore IRSProfile.domain u0 u1 g
  let V := highSourceHull IRSProfile.domain u0 u1 g
  let c := canonicalCoreContact u0 u1 g
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  have hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H = c :=
    rfl
  have hHtotal : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualTotalWeights H = t :=
    rfl
  have hHys : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualYSWeights H = y :=
    rfl
  have hHs : MvPolynomial.weightedTotalDegree
      ContactIdentityResidualGlobalFlagResearch.residualSWeights H = r :=
    rfl
  have hH : H ≠ 0 := by
    exact canonicalHighSourceCore_ne_zero_of_fixed
      IRSProfile.domain u0 u1 g source.source_ne_zero
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
    have hy := cell.y_lower
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
    have hgammaGamma :=
      commonCoreNonzeroSeeds_subset H selected Gamma hgamma
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
    have hgammaGamma :=
      commonCoreNonzeroSeeds_subset H selected Gamma hgamma
    have hcore : specialization K (selected gamma) gamma H ≠ 0 :=
      (Finset.mem_filter.mp hgamma).2
    exact highSourceHull_quotient_specializes_zero
      IRSProfile.domain u0 u1 g
      (highSourceBasis IRSProfile.domain u0 u1 g)
      (selected gamma) gamma
      (semantics.support gamma)
      (semantics.selected_degree gamma hgammaGamma)
      (semantics.agreement_card gamma hgammaGamma)
      (semantics.agreement_values gamma hgammaGamma)
      (source.source_vanishes gamma hgammaGamma) hcore v R hfactor
  have residualCount : ResidualCountProvider V g H selected Gamma
      1706 66 14
      ((thirdStage t y r).regularCountCap + (thirdPivot t r).countCap) := by
    apply residualCountProvider_of_third_residual V g H Q T selected Gamma
      1706 66 14 t y r
      (ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.t_ge_897_for_third
        cell) cell.t_le_1659
      cell.y_lower cell.y_upper
      (ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.r_ge_8_for_third
        cell) cell.r_upper
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
    · simpa only [H] using hnoPencil
  have hresidual :
      (commonCoreNonzeroSeeds H selected Gamma).card ≤
        (thirdStage t y r).regularCountCap + (thirdPivot t r).countCap := by
    have hsourceHigh :
        reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
          nestedFiveCapCoefficientBox K 11458062 131071 1706 66 14 := by
      apply nestedFiveCapCoefficientBox_mono_D
        (F := K) (Dlow :=
          48 * ContactAnchoredOneFamilySelector6750Research.agreements)
      · norm_num [ContactAnchoredOneFamilySelector6750Research.agreements]
      · exact source.source_mem_fiveCap
    exact residualCount source.source_ne_zero hsourceHigh hgV hcancel
  have hanchored :
      (commonCoreZeroSeeds H selected Gamma).card ≤ anchoredCap := by
    apply HardCell.commonCoreZeroSeeds_card_le_of_highSourceHull
      cell IRSProfile.domain u0 u1 hcardI g
      source.source_ne_zero source.source_mem_fiveCap
      hHcontact hHtotal hHys hHs selected Gamma semantics anchoredCap
    simpa only [H, c, t, y, r] using stageBound
  apply card_le_anchoredCap_add_residualCap H selected Gamma anchoredCap
    ((thirdStage t y r).regularCountCap + (thirdPivot t r).countCap)
  · exact hanchored
  · exact hresidual

 

theorem fixedSeeds_card_le_of_canonicalHighSource_uniform
    (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (stageBound : CanonicalHighSourceStageBound u0 u1 g selected Gamma
      ContactRouterUniformCaps6750Research.hardAnchoredCap)
    (hnoPencil : NoLargeSelectedPencil selected
      (commonCoreNonzeroSeeds
        (canonicalHighSourceCore IRSProfile.domain u0 u1 g)
        selected Gamma) w errors) :
    Gamma.card ≤ ContactRouterUniformCaps6750Research.hardAnchoredCap +
      ContactRouterUniformCaps6750Research.hardThirdCap := by
  have hexact := fixedSeeds_card_le_of_canonicalHighSource
    u0 u1 g selected Gamma source semantics cell
    ContactRouterUniformCaps6750Research.hardAnchoredCap stageBound hnoPencil
  exact hexact.trans (Nat.add_le_add_left
    (ContactCanonicalHighSourceUniformThirdCap6750Research.HardCell.thirdCost_le_hardThirdCap
      cell)
    ContactRouterUniformCaps6750Research.hardAnchoredCap)

end

end ContactAnchoredCanonicalHighSourceEndToEnd6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.t_ge_897_for_third
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research.highSource_thirdPivot_allFactors_card_lt_field
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research.fixedSeeds_card_le_of_canonicalHighSource
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research.fixedSeeds_card_le_of_canonicalHighSource_uniform
