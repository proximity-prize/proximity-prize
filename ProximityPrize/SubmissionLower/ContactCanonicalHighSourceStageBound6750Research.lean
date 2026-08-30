import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredCanonicalHighSourceEndToEnd6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryFixedCell6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredOrdinaryProperProvider6750Research
import ProximityPrize.SubmissionLower.ContactCanonicalHighSourceAnchoredCap6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredParentCapAdapters6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredShellSelector6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactCanonicalHighSourceStageBound6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation ContactPrimeSeedIncidence ContactInterpolation
open ContactFactorCaps ContactIdentityResidualGlobalFlagResearch
open ContactFlagInterpolation6641Research
open ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactFlagBezout6543Research ContactGCDCumulativeFlagsResearch
open ContactGlobalSelectedFamilies6600Research
open ContactTightSingularLedgerResearch
open ContactTwoTailParameters6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactAnchoredHighKernelSelectorRealization6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactCommonCoreBranchPartition6750Research
open ContactAnchoredTwoSingularUnion6750Research
open ContactAnchoredFixedBranchAssembly6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighSourceAssembly6750Research
open ContactAnchoredThirdResidualAdapter6750Research
open ContactAnchoredParentCapAdapters6750Research
open ContactAnchoredOrdinaryFixedCell6750Research
open ContactAnchoredOrdinaryProperProvider6750Research
open ContactRouterCellCosts6750Research
open ContactCanonicalHighSourceAnchoredCap6750Research
open ContactAnchoredCanonicalHighSourceEndToEnd6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev Poly4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600

 

 
theorem residualSupportData_cell_of_exact
    (F : Poly4) (t y r : Nat)
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (ht : MvPolynomial.weightedTotalDegree residualTotalWeights F = t)
    (hy : MvPolynomial.weightedTotalDegree residualYSWeights F = y)
    (hr : MvPolynomial.weightedTotalDegree residualSWeights F = r) :
    ResidualSupportData (cellSupport t y r) F := by
  refine ⟨?_, ?_, ?_⟩
  · change MvPolynomial.weightedTotalDegree residualSWeights F ≤ r - 2 + 2
    omega
  · change MvPolynomial.weightedTotalDegree residualYSWeights F ≤
      y - r - 1 + (r - 2) + 3
    omega
  · change MvPolynomial.weightedTotalDegree residualTotalWeights F ≤
      t - y + (y - r - 1) + (r - 2) + 3
    omega

 

theorem residualSupportData_cell_of_fiveCap
    (F : Poly4) {D0 w0 t y r : Nat}
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t)
    (hbox : F ∈ nestedFiveCapCoefficientBox K D0 w0 t y r) :
    ResidualSupportData (cellSupport t y r) F := by
  have hs : MvPolynomial.weightedTotalDegree residualSWeights F ≤ r := by
    apply (weightedTotalDegree_le_iff residualSWeights F r).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w0 * d 1 + (w0 - 1) * d 2 < D0 at h
    rw [weight_fin4]
    simpa [residualSWeights] using h.2.2.1
  have hys : MvPolynomial.weightedTotalDegree residualYSWeights F ≤ y := by
    apply (weightedTotalDegree_le_iff residualYSWeights F y).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w0 * d 1 + (w0 - 1) * d 2 < D0 at h
    rw [weight_fin4]
    simpa [residualYSWeights, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h.2.1
  have htotal : MvPolynomial.weightedTotalDegree residualTotalWeights F ≤ t := by
    apply (weightedTotalDegree_le_iff residualTotalWeights F t).mpr
    intro d hd
    have h := hbox hd
    change d 1 + d 2 + d 3 ≤ t ∧ d 1 + d 2 ≤ y ∧
      d 2 ≤ r ∧ d 0 + w0 * d 1 + (w0 - 1) * d 2 < D0 at h
    rw [weight_fin4]
    simpa [residualTotalWeights, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h.1
  refine ⟨?_, ?_, ?_⟩
  · change MvPolynomial.weightedTotalDegree residualSWeights F ≤ r - 2 + 2
    omega
  · change MvPolynomial.weightedTotalDegree residualYSWeights F ≤
      y - r - 1 + (r - 2) + 3
    omega
  · change MvPolynomial.weightedTotalDegree residualTotalWeights F ≤
      t - y + (y - r - 1) + (r - 2) + 3
    omega

 

theorem globalBox_tighten_to_exact_residual
    (F : Poly4) {D0 w0 L0 S0 t r : Nat}
    (hD : 0 < D0)
    (hbox : F ∈ ContactInterpolation.globalCoefficientBox K D0 w0 L0 S0)
    (ht : MvPolynomial.weightedTotalDegree residualTotalWeights F = t)
    (hr : MvPolynomial.weightedTotalDegree residualSWeights F = r) :
    F ∈ ContactInterpolation.globalCoefficientBox K D0 w0 t r := by
  have hcaps := (mem_globalCoefficientBox_iff F D0 w0 L0 S0 hD).mp hbox
  apply (mem_globalCoefficientBox_iff F D0 w0 t r hD).mpr
  refine ⟨?_, ?_, hcaps.2.2⟩
  · apply (weightedTotalDegree_le_iff seedWeights F t).mpr
    intro d hd
    have htotal := (MvPolynomial.le_weightedTotalDegree
      residualTotalWeights hd).trans ht.le
    rw [seed_weight]
    have htotal' : d 1 + d 2 + d 3 ≤ t := by
      simpa [weight_fin4, residualTotalWeights, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using htotal
    omega
  · simpa [slopeWeights, residualSWeights] using hr.le

 

theorem agreement_count_of_semantics
    (u0 u1 : I → K) (selected : K → Polynomial K) (Gamma : Finset K)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    {gamma : K} (hgamma : gamma ∈ Gamma) :
    ContactTwoTailParameters6750Research.agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
      (selected gamma).eval (IRSProfile.domain i) =
        u0 i + gamma * u1 i)).card := by
  apply (semantics.agreement_card gamma hgamma).trans
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, semantics.agreement_values gamma hgamma i hi⟩

 

theorem OrdinaryHardCell.r_ge_8
    {t y r : Nat} (cell : OrdinaryHardCell t y r) : 8 ≤ r := by
  have hmin : 8 ≤ hostileMinR y := by
    unfold hostileMinR
    split_ifs <;> omega
  exact hmin.trans cell.2.2.1

theorem OrdinaryHardCell.t_ge_897
    {t y r : Nat} (cell : OrdinaryHardCell t y r) : 897 ≤ t := by
  rcases cell.hard_or_firstDerivativeShell with hhard | hshell
  · exact ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.t_ge_897_for_third hhard
  · omega

theorem OrdinaryHardCell.selector_inputs
    {t y r : Nat} (cell : OrdinaryHardCell t y r) :
    t ≤ familyBaseTotal ∧
      familyYSCap - y ≤ familyBaseTotal - t ∧
      0 < selectorSlope y r := by
  by_cases hhard : HardCell t y r
  · exact hhard.selector_inputs
  · exact FirstDerivativeShell.selector_inputs ⟨cell, hhard⟩

theorem OrdinaryHardCell.quotient_caps
    {t y r : Nat} (cell : OrdinaryHardCell t y r) :
    selectedTotal t y r - t ≤ 2530 ∧
      familyYSCap - y ≤ 46 ∧
      familySlopeCap - r ≤ 10 ∧
      2524503 ≤ quotientWeightedCut y r := by
  by_cases hhard : HardCell t y r
  · exact hhard.quotient_caps
  · exact FirstDerivativeShell.quotient_caps ⟨cell, hhard⟩

 



theorem singularProfileValidity_of_ordinaryRed_bounds
    (D t r : Nat) (hDlo : w + 1 ≤ D)
    (hDhi : D ≤ profileA.weightedCap)
    (htLo : 1 ≤ t) (htHi : t ≤ 2530)
    (hrLo : 1 ≤ r) (hrHi : r ≤ 14) :
    SingularProfileValidity (cellTightProfile D t r) := by
  have hkLo : 1 ≤ 2 * r - 1 := by omega
  have hkHi : 2 * r - 1 ≤ 27 := by omega
  have hDnum : D ≤ 8548548 := by
    simpa [profileA, Profile.weightedCap,
      ContactTwoTailParameters6750Research.agreements, n, errors] using hDhi
  have himp : (cellTightProfile D t r).implicitYCap ≤ 1761 := by
    simp only [cellTightProfile, TightParameters.implicitYCap,
      TightParameters.kappa]
    rw [← Nat.lt_succ_iff]
    apply (Nat.div_lt_iff_lt_mul (by norm_num [w])).mpr
    have hkD : (2 * r - 1) * D ≤ 27 * 8548548 :=
      Nat.mul_le_mul hkHi hDnum
    norm_num [w]
    omega
  have halg : (cellTightProfile D t r).algebraicCap ≤ 68310 := by
    simp only [cellTightProfile, TightParameters.algebraicCap,
      TightParameters.kappa]
    exact (Nat.mul_le_mul hkHi htHi).trans (by norm_num)
  refine
    { one_le_s := by simpa [cellTightProfile] using hrLo
      s_small := by simpa [cellTightProfile] using
        hrHi.trans_lt (by norm_num [prime])
      one_le_w := by norm_num [cellTightProfile, w]
      w_small := by norm_num [cellTightProfile, w, prime]
      contact_room := by
        change w < (2 * r - 1) * D
        have hDw : w < D := by omega
        nlinarith
      algebraic_pos := by
        change 1 ≤ (2 * r - 1) * t
        exact Nat.mul_pos hkLo htLo
      implicit_small := by
        exact himp.trans_lt (by norm_num [prime])
      algebraic_small := by
        exact halg.trans_lt (by norm_num [prime])
      mixed_small := by
        exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp) halg).trans_lt
          (by norm_num [prime])
      w_lt_a := by
        norm_num [cellTightProfile, w,
          ContactTwoTailParameters6750Research.agreements, n, errors]
      a_le_n := by
        norm_num [cellTightProfile,
          ContactTwoTailParameters6750Research.agreements, n, errors] }

 

 





theorem canonicalHighSourceStageBoundExact_of_ordinaryHard_geometry
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : OrdinaryHardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (properLeft : ProperStageProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (properRight : ProperStageProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    CanonicalHighSourceStageBound u0 u1 g selected Gamma
      (canonicalAnchoredCost
        (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g)
        (canonicalCoreS u0 u1 g)) := by
  let H : Poly4 := canonicalHighSourceCore IRSProfile.domain u0 u1 g
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  let tq := quotientTotal t y r
  let yq := quotientYS y
  let rq := quotientS r
  let Dq := quotientContact y r
  have hcell : OrdinaryHardCell t y r := by simpa [t, y, r] using cell
  have hH : H ≠ 0 := by
    exact canonicalHighSourceCore_ne_zero_of_fixed IRSProfile.domain u0 u1 g
      source.source_ne_zero
  have hrH : 2 ≤ r := by
    exact (show 2 ≤ 8 by omega).trans
      (OrdinaryHardCell.r_ge_8 hcell)
  have hryH : r < y := by
    have := hcell.1
    have := hcell.2.2.2.1
    omega
  have hytH : y ≤ t := by
    have htlo := OrdinaryHardCell.t_ge_897 hcell
    have hyhi := hcell.2.1
    omega
  have identityLeft : IdentityCellBudget6750 t y r := by
    apply identityCellBudget_of_basis
    exact identityBasisBudget_of_basic_cell_analytic t y r hrH hryH hytH
  have htq : tq ≤ 2530 := by
    exact (OrdinaryHardCell.quotient_caps hcell).1
  have hyq : yq ≤ 65 := by
    change familyYSCap - y ≤ 65
    exact (OrdinaryHardCell.quotient_caps hcell).2.1.trans (by omega)
  have hrq : rq ≤ 14 := by
    change familySlopeCap - r ≤ 14
    exact (OrdinaryHardCell.quotient_caps hcell).2.2.1.trans (by omega)
  have hrq2 : 2 ≤ rq := by
    dsimp [rq, quotientS]
    have := hcell.2.2.2.1
    norm_num [familySlopeCap]
    omega
  have hrqyq : rq < yq := by
    dsimp [rq, yq, quotientS, quotientYS]
    have hyhi := hcell.2.1
    have hrlo := OrdinaryHardCell.r_ge_8 hcell
    norm_num [familySlopeCap, familyYSCap]
    omega
  have hyqtq : yq ≤ tq := by
    have hface := (OrdinaryHardCell.selector_inputs hcell).2.1
    dsimp [tq, yq, quotientTotal, quotientYS]
    unfold selectedTotal
    omega
  have identityRight : IdentityCellBudget6750 tq yq rq := by
    apply identityCellBudget_of_basis
    exact identityBasisBudget_of_basic_cell_analytic
      tq yq rq hrq2 hrqyq hyqtq
  have hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights H = t := rfl
  have hHys : MvPolynomial.weightedTotalDegree residualYSWeights H = y := rfl
  have hHs : MvPolynomial.weightedTotalDegree residualSWeights H = r := rfl
  have Hsupport : ResidualSupportData (cellSupport t y r) H :=
    residualSupportData_cell_of_exact H t y r hrH hryH hytH
      hHtotal hHys hHs
  have hsourceGlobal : reconstruct K 11094924 131071 familyMaxTotal 18 g ∈
      ContactInterpolation.globalCoefficientBox K profileA.weightedCap w 1666 14 := by
    have hcap :
        47 * ContactAnchoredOneFamilySelector6750Research.agreements ≤
          profileA.weightedCap := by
      norm_num [ContactAnchoredOneFamilySelector6750Research.agreements,
        profileA, Profile.weightedCap,
        ContactTwoTailParameters6750Research.agreements,
        ContactTwoTailParameters6750Research.n,
        ContactTwoTailParameters6750Research.errors]
    apply fiveCap_mem_globalCoefficientBox_of_caps
      (D' := profileA.weightedCap) (L' := 1666) (S' := 14)
      hcap le_rfl le_rfl
    exact source.source_mem_fiveCap
  have hHwide : H ∈ ContactInterpolation.globalCoefficientBox K
      profileA.weightedCap w 1666 14 := by
    apply mem_globalCoefficientBox_of_dvd H
      (reconstruct K 11094924 131071 familyMaxTotal 18 g)
      profileA.weightedCap w 1666 14 source.source_ne_zero
    · exact canonicalHighSourceCore_dvd_fixed_reconstruct
        IRSProfile.domain u0 u1 g
    · exact hsourceGlobal
  have hHBox : H ∈ ContactInterpolation.globalCoefficientBox K
      profileA.weightedCap w t r :=
    globalBox_tighten_to_exact_residual H
      (by norm_num [profileA, Profile.weightedCap,
        ContactTwoTailParameters6750Research.agreements,
        ContactTwoTailParameters6750Research.n,
        ContactTwoTailParameters6750Research.errors,
        ContactAnchoredOneFamilySelector6750Research.agreements]) hHwide
      hHtotal hHs
  intro theta Q htheta hQ hfactor hQfive
  let Delta := commonCoreZeroSeeds H selected Gamma
  let Good := anchoredGoodSeeds H Q selected Delta
  have hDelta : Delta ⊆ Gamma := by
    exact commonCoreZeroSeeds_subset H selected Gamma
  have hGoodDelta : Good ⊆ Delta := Finset.filter_subset _ _
  have hGood : Good ⊆ Gamma := hGoodDelta.trans hDelta
  have hdegreeDelta : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    exact semantics.selected_degree gamma (hDelta hgamma)
  have hagreementDelta : ∀ gamma ∈ Delta,
      ContactTwoTailParameters6750Research.agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    exact agreement_count_of_semantics u0 u1 selected Gamma semantics
      (hDelta hgamma)
  have hdegreeGood : ∀ gamma ∈ Good,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    exact semantics.selected_degree gamma (hGood hgamma)
  have hagreementGood : ∀ gamma ∈ Good,
      ContactTwoTailParameters6750Research.agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    exact agreement_count_of_semantics u0 u1 selected Gamma semantics
      (hGood hgamma)
  have hnoDelta : NoLargeSelectedPencil selected Delta w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono
      selected Gamma Delta w errors hDelta hnoPencil
  have hnoGood : NoLargeSelectedPencil selected Good w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono
      selected Gamma Good w errors hGood hnoPencil
  have hcontactLower : w * y - r ≤
      MvPolynomial.weightedTotalDegree (contactWeights w) H := by
    simpa [y, r, H, canonicalCoreYS, canonicalCoreS] using
      ContactResidualContactDegree6750Research.residualYS_mul_sub_residualS_le_contact
        w (by norm_num [w]) H hH
  have hDq : 11044110 -
      MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ Dq := by
    dsimp [Dq, quotientContact, quotientWeightedCut]
    simp only [w] at hcontactLower
    norm_num [familyMultiplicity,
      ContactTwoTailParameters6750Research.agreements,
      ContactAnchoredOneFamilySelector6750Research.agreements,
      contactSlope, cutWidth]
      at hcontactLower ⊢
    omega
  have hQfiveCell : Q ∈ nestedFiveCapCoefficientBox K
      (11044110 - MvPolynomial.weightedTotalDegree
        (contactWeights 131071) H) w tq yq rq := by
    simpa [H, t, y, r, tq, yq, rq, quotientTotal, quotientYS, quotientS,
      canonicalCoreContact,
      canonicalCoreTotal, canonicalCoreYS, canonicalCoreS, w] using hQfive
  have hQbox : Q ∈ ContactInterpolation.globalCoefficientBox K Dq w tq rq := by
    apply fiveCap_mem_globalCoefficientBox_of_caps hDq le_rfl le_rfl
    exact hQfiveCell
  have hDqUpper : Dq ≤ profileA.weightedCap := by
    have hylo := hcell.1
    have hrhi := hcell.2.2.2.1
    have hinner : 4980684 ≤ contactSlope * y - r := by
      norm_num [contactSlope]
      omega
    have hfirst := Nat.sub_le_sub_left hinner
      (familyMultiplicity *
        ContactAnchoredOneFamilySelector6750Research.agreements)
    have hsecond := Nat.sub_le_sub_right hfirst cutWidth
    calc
      Dq = familyMultiplicity *
            ContactAnchoredOneFamilySelector6750Research.agreements -
            (contactSlope * y - r) - cutWidth := by
              rfl
      _ ≤ familyMultiplicity *
            ContactAnchoredOneFamilySelector6750Research.agreements -
            4980684 - cutWidth := hsecond
      _ ≤ profileA.weightedCap := by
        norm_num [profileA, Profile.weightedCap, familyMultiplicity,
          ContactTwoTailParameters6750Research.agreements,
          ContactTwoTailParameters6750Research.n,
          ContactTwoTailParameters6750Research.errors,
          ContactAnchoredOneFamilySelector6750Research.agreements,
          cutWidth]
  have hQboxWide : Q ∈ ContactInterpolation.globalCoefficientBox K
      profileA.weightedCap w tq rq := by
    apply ContactFixedOrdinaryQuotientExistence6750Research.globalCoefficientBox_mono_weighted
      (F := K) (Dlow := Dq)
    · exact hDqUpper
    · exact hQbox
  have Qsupport : ResidualSupportData (cellSupport tq yq rq) Q := by
    apply residualSupportData_cell_of_fiveCap Q hrq2 hrqyq hyqtq
    exact hQfiveCell
  have leftRegular : ∀ R : ContactRegularFactorFlag6600Research.RegularIndex H,
      (regularSeeds H selected Good R).card ≤
        flagMixed (regularCumulativeFlag H R)
          (cellFirstTail t y r) (cellSecondTail t y r) := by
    intro R
    exact regular_factor_seed_bound t y r
      (hcell.2.2.2.2.2.trans (by omega)) hcell.2.1
      hcell.2.2.2.1 hrH hryH hytH properLeft identityLeft H hH hHBox
      Hsupport selected Good u0 u1 hdegreeGood hagreementGood hnoGood R
  have rightRegular : ∀ R : ContactRegularFactorFlag6600Research.RegularIndex Q,
      (regularSeeds Q selected Good R).card ≤
        flagMixed (regularCumulativeFlag Q R)
          (cellFirstTail tq yq rq) (cellSecondTail tq yq rq) := by
    intro R
    exact regular_factor_seed_bound tq yq rq htq hyq hrq hrq2 hrqyq hyqtq
      properRight identityRight Q hQ hQboxWide Qsupport selected Good u0 u1
      hdegreeGood hagreementGood hnoGood R
  let PH := cellTightProfile profileA.weightedCap t r
  let PQ := cellTightProfile Dq tq rq
  have validH : SingularProfileValidity PH := by
    apply singularProfileValidity_of_ordinaryRed_bounds
    · norm_num [w, profileA, Profile.weightedCap,
        ContactTwoTailParameters6750Research.agreements,
        ContactTwoTailParameters6750Research.n,
        ContactTwoTailParameters6750Research.errors]
    · exact le_rfl
    · omega
    · exact hcell.2.2.2.2.2.trans (by omega)
    · omega
    · exact hcell.2.2.2.1
  have validQ : SingularProfileValidity PQ := by
    apply singularProfileValidity_of_ordinaryRed_bounds
    · have hlow := (OrdinaryHardCell.quotient_caps hcell).2.2.2
      change w + 1 ≤ quotientWeightedCut y r
      norm_num [w] at ⊢
      omega
    · exact hDqUpper
    · omega
    · exact htq
    · omega
    · exact hrq
  have singularHBound :
      (anchoredSingularGSeeds H selected Delta).card ≤ PH.countCap := by
    apply anchoredSingularGSeeds_card_le_countCap PH H hH hHBox
      validH.one_le_s validH.s_small validH.one_le_w validH.w_small
      validH.contact_room validH.algebraic_pos validH.implicit_small
      validH.algebraic_small validH.mixed_small validH.w_lt_a validH.a_le_n
      selected Delta (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
    · simp [PH, cellTightProfile, I, n]
    · exact hdegreeDelta
    · exact hagreementDelta
    · simpa [PH, cellTightProfile, TightParameters.errors,
        ContactTwoTailParameters6750Research.errors,
        ContactTwoTailParameters6750Research.n,
        ContactTwoTailParameters6750Research.agreements] using hnoDelta
  have singularQBound :
      (anchoredSingularQSeeds H Q selected Delta).card ≤ PQ.countCap := by
    apply anchoredSingularQSeeds_card_le_countCap PQ H Q hQ hQbox
      validQ.one_le_s validQ.s_small validQ.one_le_w validQ.w_small
      validQ.contact_room validQ.algebraic_pos validQ.implicit_small
      validQ.algebraic_small validQ.mixed_small validQ.w_lt_a validQ.a_le_n
      selected Delta (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
    · simp [PQ, cellTightProfile, I, n]
    · exact hdegreeDelta
    · exact hagreementDelta
    · simpa [PQ, cellTightProfile, TightParameters.errors,
        ContactTwoTailParameters6750Research.errors,
        ContactTwoTailParameters6750Research.n,
        ContactTwoTailParameters6750Research.agreements] using hnoDelta
  let C : AnchoredStageCertificate H Q selected Delta :=
    { supportH := cellSupport t y r
      supportQ := cellSupport tq yq rq
      pH := cellFixedFlag t y r
      qH := cellFirstTail t y r
      rH := cellSecondTail t y r
      pQ := cellFixedFlag tq yq rq
      qQ := cellFirstTail tq yq rq
      rQ := cellSecondTail tq yq rq
      singularH := PH.countCap
      singularQ := PQ.countCap
      Hsupport := Hsupport
      Qsupport := Qsupport
      singularH_bound := singularHBound
      singularQ_bound := singularQBound
      regularH_bound := leftRegular
      regularQ_bound := rightRegular
      H_s_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega
      H_ys_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega
      H_total_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega
      Q_s_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega
      Q_ys_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega
      Q_total_le := by simp [cellSupport, cellFixedFlag, cellA, cellB, cellS,
        ContactMovingAgreementCertificate6719Research.support,
        ContactMovingPositiveLedger6719Research.surfaceFlag] <;> omega }
  refine ⟨C, ?_⟩
  simp [C, AnchoredStageCertificate.cost, PH, PQ, canonicalAnchoredCost,
    cellRegularCost, t, y, r, tq, yq, rq, Dq, quotientContact]

 

theorem canonicalHighSourceStageBound_of_cell_geometry
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (properLeft : ProperStageProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (properRight : ProperStageProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    CanonicalHighSourceStageBound u0 u1 g selected Gamma
      ContactRouterUniformCaps6750Research.hardAnchoredCap := by
  intro theta Q htheta hQ hfactor hQbox
  obtain ⟨C, hC⟩ :=
    canonicalHighSourceStageBoundExact_of_ordinaryHard_geometry
      u0 u1 g selected Gamma source semantics
        (ContactOrdinaryHardShell6750Research.HardCell.ordinaryHardCell cell)
        hnoPencil properLeft properRight theta Q htheta hQ hfactor hQbox
  refine ⟨C, hC.trans ?_⟩
  exact
    ContactCanonicalHighSourceAnchoredCap6750Research.HardCell.canonicalAnchoredCost_le_hardAnchoredCap
      cell

 

theorem canonicalHighSourceStageBoundExact_of_ordinaryHard_tangents
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : OrdinaryHardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (tangentLeft : CellTangentProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (tangentRight : CellTangentProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    CanonicalHighSourceStageBound u0 u1 g selected Gamma
      (canonicalAnchoredCost
        (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g)
        (canonicalCoreS u0 u1 g)) := by
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  have hcell : OrdinaryHardCell t y r := by simpa [t, y, r] using cell
  have hr2 : 2 ≤ r := by
    exact (show 2 ≤ 8 by omega).trans (OrdinaryHardCell.r_ge_8 hcell)
  have hry : r < y := by
    have hylo := hcell.1
    have hrhi := hcell.2.2.2.1
    omega
  have hyt : y ≤ t := by
    have htlo := OrdinaryHardCell.t_ge_897 hcell
    have hyhi := hcell.2.1
    omega
  have properLeft : ProperStageProvider6750 t y r :=
    properStageProvider6750_of_tangent t y r
      (hcell.2.2.2.2.2.trans (by omega)) hcell.2.1 hcell.2.2.2.1
      hr2 hry hyt (by simpa [t, y, r] using tangentLeft)
  let tq := quotientTotal t y r
  let yq := quotientYS y
  let rq := quotientS r
  have htq : tq ≤ 2530 := (OrdinaryHardCell.quotient_caps hcell).1
  have hyq : yq ≤ 65 :=
    (OrdinaryHardCell.quotient_caps hcell).2.1.trans (by omega)
  have hrq : rq ≤ 14 :=
    (OrdinaryHardCell.quotient_caps hcell).2.2.1.trans (by omega)
  have hrq2 : 2 ≤ rq := by
    dsimp [rq, quotientS]
    have hrhi := hcell.2.2.2.1
    norm_num [familySlopeCap]
    omega
  have hrqyq : rq < yq := by
    dsimp [rq, yq, quotientS, quotientYS]
    have hyhi := hcell.2.1
    have hrlo := OrdinaryHardCell.r_ge_8 hcell
    norm_num [familySlopeCap, familyYSCap]
    omega
  have hyqtq : yq ≤ tq := by
    have hface := (OrdinaryHardCell.selector_inputs hcell).2.1
    dsimp [tq, yq, quotientTotal, quotientYS]
    unfold selectedTotal
    omega
  have properRight : ProperStageProvider6750 tq yq rq :=
    properStageProvider6750_of_tangent tq yq rq htq hyq hrq hrq2 hrqyq hyqtq
      (by simpa [t, y, r, tq, yq, rq] using tangentRight)
  exact canonicalHighSourceStageBoundExact_of_ordinaryHard_geometry
    u0 u1 g selected Gamma source semantics cell hnoPencil
      properLeft properRight

 


theorem canonicalHighSourceStageBound_of_cell_tangents
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (tangentLeft : CellTangentProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (tangentRight : CellTangentProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    CanonicalHighSourceStageBound u0 u1 g selected Gamma
      ContactRouterUniformCaps6750Research.hardAnchoredCap := by
  let t := canonicalCoreTotal u0 u1 g
  let y := canonicalCoreYS u0 u1 g
  let r := canonicalCoreS u0 u1 g
  have hcell : HardCell t y r := by simpa [t, y, r] using cell
  have hr2 : 2 ≤ r := by
    exact (show 2 ≤ 8 by omega).trans
      (ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.r_ge_8_for_third
        hcell)
  have hry : r < y := by
    have hylo := hcell.y_lower
    have hrhi := hcell.r_upper
    omega
  have hyt : y ≤ t := by
    have htlo := ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.t_ge_897_for_third
      hcell
    have hyhi := hcell.y_upper
    omega
  have properLeft : ProperStageProvider6750 t y r :=
    properStageProvider6750_of_tangent t y r
      (hcell.t_le_1659.trans (by omega)) hcell.y_upper hcell.r_upper
      hr2 hry hyt (by simpa [t, y, r] using tangentLeft)
  let tq := quotientTotal t y r
  let yq := quotientYS y
  let rq := quotientS r
  have htq : tq ≤ 2530 := hcell.quotient_caps.1
  have hyq : yq ≤ 65 := hcell.quotient_caps.2.1.trans (by omega)
  have hrq : rq ≤ 14 := hcell.quotient_caps.2.2.1.trans (by omega)
  have hrq2 : 2 ≤ rq := by
    dsimp [rq, quotientS]
    have hrhi := hcell.r_upper
    norm_num [familySlopeCap]
    omega
  have hrqyq : rq < yq := by
    dsimp [rq, yq, quotientS, quotientYS]
    have hyhi := hcell.y_upper
    have hrlo := ContactAnchoredCanonicalHighSourceEndToEnd6750Research.HardCell.r_ge_8_for_third
      hcell
    norm_num [familySlopeCap, familyYSCap]
    omega
  have hyqtq : yq ≤ tq := by
    have hface := hcell.selector_inputs.2.1
    dsimp [tq, yq, quotientTotal, quotientYS]
    unfold selectedTotal
    omega
  have properRight : ProperStageProvider6750 tq yq rq :=
    properStageProvider6750_of_tangent tq yq rq htq hyq hrq hrq2 hrqyq hyqtq
      (by simpa [t, y, r, tq, yq, rq] using tangentRight)
  exact canonicalHighSourceStageBound_of_cell_geometry
    u0 u1 g selected Gamma source semantics cell hnoPencil
      properLeft properRight

 

theorem fixedSeeds_card_le_of_canonicalHighSource_cell_geometry
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (properLeft : ProperStageProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (properRight : ProperStageProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    Gamma.card ≤ ContactRouterUniformCaps6750Research.hardAnchoredCap +
      ContactRouterUniformCaps6750Research.hardThirdCap := by
  have hstage := canonicalHighSourceStageBound_of_cell_geometry
    u0 u1 g selected Gamma source semantics cell hnoPencil properLeft properRight
  have hnonzero : NoLargeSelectedPencil selected
      (commonCoreNonzeroSeeds
        (canonicalHighSourceCore IRSProfile.domain u0 u1 g) selected Gamma)
      w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono selected Gamma _ w errors
      (commonCoreNonzeroSeeds_subset _ selected Gamma) hnoPencil
  exact fixedSeeds_card_le_of_canonicalHighSource_uniform
    u0 u1 g selected Gamma source semantics cell hstage hnonzero

 
theorem fixedSeeds_card_le_of_canonicalHighSource_cell_tangents
    (u0 u1 : I → K)
    (g : ContactFlagInterpolation6641Research.CoefficientIndex
      11094924 131071 familyMaxTotal 18 → K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (source : FixedHighSourceCertificate g selected Gamma)
    (semantics : FixedCandidateSemantics IRSProfile.domain u0 u1
      selected Gamma)
    (cell : HardCell
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (tangentLeft : CellTangentProvider6750
      (canonicalCoreTotal u0 u1 g)
      (canonicalCoreYS u0 u1 g)
      (canonicalCoreS u0 u1 g))
    (tangentRight : CellTangentProvider6750
      (quotientTotal (canonicalCoreTotal u0 u1 g)
        (canonicalCoreYS u0 u1 g) (canonicalCoreS u0 u1 g))
      (quotientYS (canonicalCoreYS u0 u1 g))
      (quotientS (canonicalCoreS u0 u1 g))) :
    Gamma.card ≤ ContactRouterUniformCaps6750Research.hardAnchoredCap +
      ContactRouterUniformCaps6750Research.hardThirdCap := by
  have hstage := canonicalHighSourceStageBound_of_cell_tangents
    u0 u1 g selected Gamma source semantics cell hnoPencil
      tangentLeft tangentRight
  have hnonzero : NoLargeSelectedPencil selected
      (commonCoreNonzeroSeeds
        (canonicalHighSourceCore IRSProfile.domain u0 u1 g) selected Gamma)
      w errors :=
    ContactProperCutSeedCount.noLargeSelectedPencil_mono selected Gamma _ w errors
      (commonCoreNonzeroSeeds_subset _ selected Gamma) hnoPencil
  exact fixedSeeds_card_le_of_canonicalHighSource_uniform
    u0 u1 g selected Gamma source semantics cell hstage hnonzero

end

end ContactCanonicalHighSourceStageBound6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceStageBound6750Research.canonicalHighSourceStageBound_of_cell_geometry
#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceStageBound6750Research.fixedSeeds_card_le_of_canonicalHighSource_cell_geometry
#print axioms ProximityPrize.SubmissionLower.ContactCanonicalHighSourceStageBound6750Research.fixedSeeds_card_le_of_canonicalHighSource_cell_tangents
