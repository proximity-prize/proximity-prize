import ProximityPrize.SubmissionLower.ContactMovingFixedStage6732Research
import ProximityPrize.SubmissionLower.ContactFirstTailReducedProper6732Research
import ProximityPrize.SubmissionLower.ContactFirstTailIdentityIncidence6731Research
import ProximityPrize.SubmissionLower.ContactIdentityCurveProvider6731Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
import ProximityPrize.SubmissionLower.ContactKernelCommonGCDResearch
import ProximityPrize.SubmissionLower.ContactKernelArithmetic6733Research
import ProximityPrize.SubmissionLower.ContactExceptionalSeedCount
namespace ProximityPrize.SubmissionLower.ContactKernelFixedSelected6733Research
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint ContactFactorCaps ContactPrimeSeedIncidence
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactOriginalRegularResidualStage6600Research
  ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research ContactResidualSupportParametersResearch
open ContactIdentityResidualIterationResearch ContactGenericSurface
open ContactTaylorNumerators
open ContactFlagBezout6543Research ContactGCDCumulativeFlagsResearch
open ContactFactoredFlagCount6676Research ContactGeometricFactorCover
open ContactRobustFixedMeet6656Research ContactMovingFactorLedger6719Research
open ContactFirstTailReducedProper6732Research ContactFirstTailIdentityIncidence6731Research
open ContactIdentityCurveProvider6731Research
open ContactProfileFixedSelectedCombinerResearch
open ContactMovingFixedProfile6732Research
open ContactNearPencil6600ArithmeticResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactKernelArithmetic6733Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactImplicitContactLift ContactCumulativeWeightedDegreeResearch
open ContactTightSingularLedgerResearch ContactSingularBranch6600Research
noncomputable section
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 40000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
def prime : ℕ := 2130706433
def fixedProfile : Profile := ⟨262144,131071,182052,7464132,1240,11⟩
def fixedSupport : ResidualSupportParameters :=
  ContactMovingAgreementCertificate6719Research.support 1186 42 9
theorem fixedSupport_eq : fixedSupport = ⟨11,54,1240,by decide,
    by decide,by decide,by decide⟩ := by rfl
private theorem fixed_degree_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k) ≤
      fixedProfile.degreeIncidence*(fixedProfile.agreements-k) := by
  have hcross := identity_degree_weight_cross_le fixedProfile.n
    fixedProfile.agreements fixedProfile.w k hk (by decide) (by decide)
  have hceiling : fixedProfile.n*fixedProfile.gap*fixedProfile.w ≤
      fixedProfile.degreeIncidence*fixedProfile.agreements := by decide
  have hmul := Nat.mul_le_mul_right (fixedProfile.agreements-k) hceiling
  have htotal : ((fixedProfile.n-k)*fixedProfile.gap*(fixedProfile.w-k))*
      fixedProfile.agreements ≤
      (fixedProfile.degreeIncidence*(fixedProfile.agreements-k))*
        fixedProfile.agreements := by
    calc
      _ = (fixedProfile.n-k)*(fixedProfile.agreements-fixedProfile.w)*
          (fixedProfile.w-k)*fixedProfile.agreements := rfl
      _ ≤ fixedProfile.n*(fixedProfile.agreements-fixedProfile.w)*fixedProfile.w*
          (fixedProfile.agreements-k) := hcross
      _ ≤ (fixedProfile.degreeIncidence*fixedProfile.agreements)*
          (fixedProfile.agreements-k) := by
        simpa only [Profile.gap] using hmul
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right htotal (by decide)
private theorem fixed_unit_part_bound (k : ℕ) (hk : k ≤ fixedProfile.w) :
    (fixedProfile.n-k)*fixedProfile.gap ≤
      fixedProfile.unitIncidence*(fixedProfile.agreements-k) := by
  simpa only [Profile.gap,Profile.unitIncidence] using
    identity_unit_weight_le fixedProfile.n fixedProfile.agreements fixedProfile.w
      k hk (by decide) (by decide)
private theorem geometric_identityDegree_pos
    {F : MvPolynomial (Fin 4) K} (g : GeometricFactor K F) :
    1 ≤ ContactMovingFixedProfile6732Research.identityDegree
      fixedProfile 1186 42 9 (geometricCumulativeFlag K g) := by
  have hirr : Irreducible g.1 :=
    (surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).1
  have hp := irreducible_positive_surface_degree g.1 hirr
  have hflag := polynomialIn_surfaceCumulativeFlag g.1
  have h0 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 0
  have h1 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 1
  have h2 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 2
  have htotal : 0 < (geometricCumulativeFlag K g).zOnly+
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all := by omega
  unfold ContactMovingFixedProfile6732Research.identityDegree
    ContactMovingOuterBudget6719Research.paddedCut
  simp only [ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    ContactFlagBezout6543Research.flagMixed,
    ContactFlagBezout6543Research.unitZFlag,
    ContactFlagBezout6543Research.unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  norm_num [fixedProfile,Profile.w]
  omega
private theorem fixedSupport_of_dvd
    (F Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (Hsupport : ResidualSupportData fixedSupport Q) :
    ResidualSupportData fixedSupport F :=
  ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans
      Hsupport.s_weight,
    (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans
      Hsupport.ys_weight,
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans
      Hsupport.total_weight⟩
private def fixedGeometricStage
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hdegree : ∀ γ ∈ Γ,(selected γ).natDegree ≤ fixedProfile.w)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    letI : CharP (GenericField K) prime := genericField_charP K prime
    ResidualStage (polynomialEmbedding K)
      (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g)
      x prime fixedProfile.errors (geometricCumulativeFlag K g) fixedProfile.w
      fixedSupport := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
    (degreeOf_R_le_of_mem_box R.1 fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap hRdata.2.2).trans_lt (by decide)
  have hsupport : ResidualSupportData fixedSupport R.1 :=
    fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
  let S := regularGeometricResidualStageOfSupport fixedSupport Q selected Γ nodes x u0 u1
    hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall hsupport (by decide) g
  exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)
private theorem geometric_flag_caps
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (R : RegularIndex Q) (g : GeometricFactor K R.1) :
    (geometricCumulativeFlag K g).all ≤ fixedSupport.s ∧
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤
        fixedSupport.ys ∧
      (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
        (geometricCumulativeFlag K g).all ≤ fixedSupport.total := by
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  exact geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
    (fixedSupport_of_dvd R.1 Q hQ
      (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport) g
theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ γ ∈ Γ,(selected γ).natDegree ≤ fixedProfile.w)
    (hagreement : ∀ γ ∈ Γ,fixedProfile.agreements ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Γ R).card*fixedProfile.gap ≤
      ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
        (regularCumulativeFlag Q R) := by
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hRdata := directFactor_data Q R.1 hQ fixedProfile.weightedCap fixedProfile.w
    fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hsolutions : ∀ γ ∈ regularSeeds Q selected Γ R,
      specialization K (selected γ) γ R.1=0 := by
    intro γ hγ
    exact (Finset.mem_filter.mp hγ).2.1
  have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Γ R) hsolutions
  have hstage : ∀ g : GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card*
        fixedProfile.gap ≤
      ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
        (geometricCumulativeFlag K g) := by
    intro g
    let S := fixedGeometricStage Q hQ hbox Hsupport selected Γ nodes x u0 u1
      hinj hdegree hnoPencil R g
    have hsub : geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g ⊆ Γ :=
      (geometricSeeds_subset K R.1 selected (regularSeeds Q selected Γ R) g).trans
        (regularSeeds_subset Q selected Γ R)
    have hnodesS : S.nodes.card=fixedProfile.n := by
      simpa [S,fixedGeometricStage,reflagResidualStage,
        regularGeometricResidualStageOfSupport,geometricResidualStageOfSupport] using hnodes
    have hagreementS : ∀ γ ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Γ R) g,
        fixedProfile.agreements ≤ (S.agreementFiber γ).card := by
      intro γ hγ
      simpa [S,ResidualStage.agreementFiber,ResidualStage.Agrees,fixedGeometricStage,
        reflagResidualStage,regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement γ (hsub hγ)
    have hf := geometric_flag_caps Q hQ hbox Hsupport R g
    by_cases htail : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (fixedProfile.w+1))
    · have hsize : S.nodes.card=fixedProfile.agreements+fixedProfile.errors := by
        rw [hnodesS]
        rfl
      have hboxS : S.F ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
          fixedProfile.seedTotalCap fixedProfile.slopeCap := by
        simpa [S,fixedGeometricStage,reflagResidualStage,
          regularGeometricResidualStageOfSupport,geometricResidualStageOfSupport] using
          hRdata.2.2
      have hprovider := actual_identityCurveCountProvider S fixedProfile.agreements
        hsize hagreementS (by decide) htail fixedProfile.weightedCap
        fixedProfile.seedTotalCap fixedProfile.slopeCap (by decide) (by decide)
        (by decide) hboxS (by
          exact ⟨hf.2.1.trans_lt (by decide),hf.1.trans_lt (by decide),
            hf.2.2.trans_lt (by decide)⟩)
        (by
          have hc := hf
          norm_num [fixedProfile,fixedSupport,prime,Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
      change IdentityCurveCountProvider S
        (ContactMovingFixedProfile6732Research.identityDegree fixedProfile 1186 42 9
          (geometricCumulativeFlag K g)) at hprovider
      have hi := identity_surface_seed_bound S fixedProfile.agreements
        (ContactMovingFixedProfile6732Research.identityDegree fixedProfile 1186 42 9
          (geometricCumulativeFlag K g)) hprovider hagreementS (by decide)
        (by rw [hnodesS]; decide) (geometric_identityDegree_pos g)
      have hi' : (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card*
          fixedProfile.gap ≤ (fixedProfile.n-fixedProfile.w)*(fixedProfile.errors+1)*
            ContactMovingFixedProfile6732Research.identityDegree fixedProfile 1186 42 9
              (geometricCumulativeFlag K g) := by
        rw [hnodesS] at hi
        simpa only [Profile.gap] using hi
      exact hi'.trans (by
        simpa [fixedProfile,ContactKernelArithmetic6733Research.fixedProfile6733]
          using ContactKernelArithmetic6733Research.identity_le_proper6733
            (geometricCumulativeFlag K g))
    · have hproper := proper_firstTail_reduced_seed_bound (polynomialEmbedding_injective K)
        fixedProfile 1186 42 9 S hnodesS hagreementS (by decide) (by decide)
        fixed_degree_part_bound fixed_unit_part_bound htail
        (by exact ⟨hf.2.1.trans_lt (by decide),hf.1.trans_lt (by decide),
          hf.2.2.trans_lt (by decide)⟩)
        (by
          have hc := hf
          norm_num [fixedProfile,fixedSupport,prime,Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
        (by
          have hc := hf
          norm_num [fixedProfile,fixedSupport,prime,Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
        (by
          have hc := hf
          norm_num [fixedProfile,fixedSupport,prime,Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
      exact hproper.trans (by
        unfold ContactKernelArithmetic6733Research.properLedger
        omega)
  calc
    _ ≤ (∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card)*
        fixedProfile.gap := Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card*
          fixedProfile.gap := by rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K R.1,
        ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
          (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hstage g)
    _ ≤ _ := by
      have hc := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact ContactKernelArithmetic6733Research.sum_properLedger_le
        fixedProfile 1186 42 9 (geometricCumulativeFlag K)
        (originalCumulativeFlag R.1) hc.1 hc.2.1 hc.2.2
def capOf (Q : MvPolynomial (Fin 4) K) : ContactKernelArithmetic6733Research.Cap :=
  ⟨wt residualTotalWeights Q,wt residualYSWeights Q,wt residualSWeights Q⟩
private theorem originalFlag_eq_flagOfCap (Q : MvPolynomial (Fin 4) K) :
    originalCumulativeFlag Q =
      ContactKernelArithmetic6733Research.flagOfCap (capOf Q) := by
  simp [originalCumulativeFlag,flagFromCaps,
    ContactKernelArithmetic6733Research.flagOfCap,capOf]
private theorem regularCumulativeFlag_budgets_exact
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    (∑ R : RegularIndex Q,(regularCumulativeFlag Q R).all) ≤
        (originalCumulativeFlag Q).all ∧
      (∑ R : RegularIndex Q,((regularCumulativeFlag Q R).yz+
        (regularCumulativeFlag Q R).all)) ≤
        (originalCumulativeFlag Q).yz+(originalCumulativeFlag Q).all ∧
      (∑ R : RegularIndex Q,((regularCumulativeFlag Q R).zOnly+
        (regularCumulativeFlag Q R).yz+(regularCumulativeFlag Q R).all)) ≤
        (originalCumulativeFlag Q).zOnly+(originalCumulativeFlag Q).yz+
          (originalCumulativeFlag Q).all := by
  have hp := positiveRFactors_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hp
  have hm := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hp
  have ht := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hp
  refine ⟨?_,?_,?_⟩
  · rw [Finset.sum_congr rfl
        (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).1),
      Finset.sum_coe_sort,
      (originalCumulativeFlag_cumulative Q).1]
    exact hs
  · rw [Finset.sum_congr rfl
        (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).2.1),
      Finset.sum_coe_sort,
      (originalCumulativeFlag_cumulative Q).2.1]
    exact hm
  · rw [Finset.sum_congr rfl
        (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).2.2),
      Finset.sum_coe_sort,
      (originalCumulativeFlag_cumulative Q).2.2]
    exact ht
private def dynamicTight (Q : MvPolynomial (Fin 4) K) :
    ContactTightSingularLedgerResearch.TightParameters :=
  ⟨262144,131071,182052,7464132,
    wt residualTotalWeights Q,max 1 (wt residualSWeights Q)⟩
theorem fixed_selected_count_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hflag : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K 7464132 131071 1240 11)
    (hys : wt residualYSWeights Q ≤ 54)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ,(selected γ).natDegree ≤ 131071)
    (hsolution : ∀ γ ∈ Γ,specialization K (selected γ) γ Q=0)
    (hagreement : ∀ γ ∈ Γ,182052 ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ 131071 80092) :
    Γ.card ≤ ContactKernelArithmetic6733Research.fixed (capOf Q)+
      ContactKernelArithmetic6733Research.singularPadded (capOf Q) (41*182052) := by
  have hcaps := (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
    Q 7464132 131071 1240 11 (by decide)).mp hflag
  have htotal : wt residualTotalWeights Q ≤ 1240 := hcaps.1
  have hslope : wt residualSWeights Q ≤ 11 := hcaps.2.1
  have hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap := by
    simpa [fixedProfile] using
      ContactFlagKernelUniversalityResearch.flag_box_to_ordinary K
        7464132 131071 1240 11 Q hflag
  have hsupport : ResidualSupportData fixedSupport Q := by
    refine ⟨?_,?_,?_⟩
    · simpa [fixedSupport,ContactMovingAgreementCertificate6719Research.support]
        using hslope
    · simpa [fixedSupport,ContactMovingAgreementCertificate6719Research.support]
        using hys
    · simpa [fixedSupport,ContactMovingAgreementCertificate6719Research.support]
        using htotal
  by_cases htotal0 : wt residualTotalWeights Q = 0
  · have htotal0' : MvPolynomial.weightedTotalDegree residualTotalWeights Q = 0 :=
      htotal0
    have hY : Q.degreeOf 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro d hd
      have ht := (hflag hd).1
      change d 1 + d 2 + d 3 ≤ 1240 at ht
      have hwt := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
      rw [ContactFactorCaps.weight_fin4] at hwt
      rw [htotal0'] at hwt
      simp [residualTotalWeights] at hwt
      omega
    have hR : Q.degreeOf 2 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro d hd
      have hwt := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
      rw [ContactFactorCaps.weight_fin4] at hwt
      rw [htotal0'] at hwt
      simp [residualTotalWeights] at hwt
      omega
    have hZ : Q.degreeOf 3 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply MvPolynomial.degreeOf_le_iff.mpr
      intro d hd
      have hwt := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
      rw [ContactFactorCaps.weight_fin4] at hwt
      rw [htotal0'] at hwt
      simp [residualTotalWeights] at hwt
      omega
    have hc := ContactExceptionalSeedCount.card_actual_solution_seeds_le
      Q hQ hY hR Γ (fun γ hγ ↦ ⟨selected γ,hsolution γ hγ⟩)
    have hzero : Γ.card = 0 := Nat.eq_zero_of_le_zero (hc.trans_eq hZ)
    simp [hzero]
  have hcover := card_le_regular_sum_add_singular fixedProfile Q hQ hbox
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    selected Γ hsolution
  have hregularEach := regular_factor_seed_bound Q hQ hbox hsupport selected Γ
    nodes x u0 u1 hinj (by simpa [fixedProfile] using hnodes)
    (by simpa [fixedProfile] using hdegree)
    (by simpa [fixedProfile] using hagreement)
    (by norm_num [fixedProfile,Profile.errors] at hnoPencil ⊢; exact hnoPencil)
  have hregScaled :
      (∑ R : RegularIndex Q,(regularSeeds Q selected Γ R).card)*fixedProfile.gap ≤
        ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
          (originalCumulativeFlag Q) := by
    calc
      _ = ∑ R : RegularIndex Q,
          (regularSeeds Q selected Γ R).card*fixedProfile.gap := by
        rw [Finset.sum_mul]
      _ ≤ ∑ R : RegularIndex Q,
          ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
            (regularCumulativeFlag Q R) :=
        Finset.sum_le_sum (fun R _ ↦ hregularEach R)
      _ ≤ _ := by
        have hc := regularCumulativeFlag_budgets_exact Q hQ
        exact ContactKernelArithmetic6733Research.sum_properLedger_le
          fixedProfile 1186 42 9 (regularCumulativeFlag Q)
          (originalCumulativeFlag Q) hc.1 hc.2.1 hc.2.2
  have hreg : (∑ R : RegularIndex Q,(regularSeeds Q selected Γ R).card) ≤
      ContactKernelArithmetic6733Research.properLedger fixedProfile 1186 42 9
        (originalCumulativeFlag Q)/fixedProfile.gap := by
    exact (Nat.le_div_iff_mul_le (by decide : 0 < fixedProfile.gap)).2 hregScaled
  let S := dynamicTight Q
  have hflagExact : Q ∈
      ContactFlagInterpolation6641Research.globalCoefficientBox K 7464132 131071
        (wt residualTotalWeights Q) (wt residualSWeights Q) := by
    apply (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
      Q 7464132 131071 (wt residualTotalWeights Q)
        (wt residualSWeights Q) (by decide)).mpr
    exact ⟨le_rfl,le_rfl,hcaps.2.2⟩
  have hboxExact : Q ∈ globalCoefficientBox K 7464132 131071
      (wt residualTotalWeights Q) (wt residualSWeights Q) :=
    ContactFlagKernelUniversalityResearch.flag_box_to_ordinary K
      7464132 131071 (wt residualTotalWeights Q) (wt residualSWeights Q)
      Q hflagExact
  have hboxS : Q ∈ globalCoefficientBox K S.D S.w S.L S.s := by
    intro d hd
    have he := hboxExact hd
    change d 1+d 3 ≤ wt residualTotalWeights Q ∧
      d 2 ≤ max 1 (wt residualSWeights Q) ∧
      d 0+131071*d 1+(131071-1)*d 2 < 7464132
    exact ⟨he.1,he.2.1.trans (le_max_right _ _),he.2.2⟩
  have hsPad : max 1 (wt residualSWeights Q) ≤ 11 :=
    max_le (by decide) hslope
  have hkPos : 1 ≤ 2 * max 1 (wt residualSWeights Q) - 1 := by omega
  have hkLe : 2 * max 1 (wt residualSWeights Q) - 1 ≤ 21 := by omega
  have htotalPos : 1 ≤ wt residualTotalWeights Q := by omega
  have hAlgPos : 1 ≤
      (2 * max 1 (wt residualSWeights Q) - 1) * wt residualTotalWeights Q :=
    by
      change 0 < (2 * max 1 (wt residualSWeights Q) - 1) *
        wt residualTotalWeights Q
      exact Nat.mul_pos hkPos htotalPos
  have hAlgLe :
      (2 * max 1 (wt residualSWeights Q) - 1) * wt residualTotalWeights Q ≤
        26040 := by
    exact (Nat.mul_le_mul hkLe htotal).trans_eq (by decide)
  have hImpLe :
      (((2 * max 1 (wt residualSWeights Q) - 1) * 7464132 - 1) / 131071) ≤
        1195 := by
    have hm := Nat.mul_le_mul_right 7464132 hkLe
    have hsub := Nat.sub_le_sub_right hm 1
    have hdiv := Nat.div_le_div_right (c := 131071) hsub
    exact hdiv.trans_eq (by decide)
  have hMixedLe :
      2 * (((2 * max 1 (wt residualSWeights Q) - 1) * 7464132 - 1) / 131071) *
        ((2 * max 1 (wt residualSWeights Q) - 1) * wt residualTotalWeights Q) ≤
        62235600 := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hImpLe) hAlgLe).trans_eq (by decide)
  have hsing :=
    ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_count_le_countCap
      S Q hQ hboxS
      (by simp [S,dynamicTight])
      (by simpa [S,dynamicTight] using hsPad.trans_lt (by decide))
      (by norm_num [S,dynamicTight])
      (by norm_num [S,dynamicTight,prime])
      (by simp [S,dynamicTight,TightParameters.kappa]; omega)
      (by simpa [S,dynamicTight,TightParameters.algebraicCap,
        TightParameters.kappa] using hAlgPos)
      (by simpa [S,dynamicTight,TightParameters.implicitYCap,
        TightParameters.kappa] using hImpLe.trans_lt (by decide))
      (by simpa [S,dynamicTight,TightParameters.algebraicCap,
        TightParameters.kappa] using hAlgLe.trans_lt (by decide))
      (by simpa [S,dynamicTight,TightParameters.implicitYCap,
        TightParameters.algebraicCap,TightParameters.kappa] using
          hMixedLe.trans_lt (by decide))
      (by norm_num [S,dynamicTight])
      (by norm_num [S,dynamicTight])
      selected Γ nodes x u0 u1 hinj
      (by simpa [S,dynamicTight] using hnodes)
      (by simpa [S,dynamicTight] using hdegree)
      (by simpa [S,dynamicTight] using hagreement)
      (by simpa [S,dynamicTight,TightParameters.errors] using hnoPencil)
  have hsingBound :
      (singularSeeds Q selected Γ).card ≤
        ContactKernelArithmetic6733Research.singularPadded (capOf Q) (41*182052) := by
    refine hsing.trans ?_
    have hpos : 0 < wt residualTotalWeights Q := Nat.pos_of_ne_zero htotal0
    simp [S,dynamicTight,ContactKernelArithmetic6733Research.singularPadded,
      ContactKernelArithmetic6733Research.ensurePositiveSlope,
      ContactKernelArithmetic6733Research.singular,
      capOf,
      ContactKernelArithmetic6733Research.agreements,
      ContactKernelArithmetic6733Research.w,
      ContactKernelArithmetic6733Research.u,
      ContactKernelArithmetic6733Research.errors,
      ContactKernelArithmetic6733Research.gap,
      ContactKernelArithmetic6733Research.n,
      TightParameters.countCap,TightParameters.tightNumerator,
      TightParameters.coreNumerator,TightParameters.aggregateCost,
      TightParameters.agreement,TightParameters.implicitYCap,
      TightParameters.algebraicCap,TightParameters.kappa,
      TightParameters.errors,TightParameters.gap,
      ContactSingularLedger6600Research.dot,pow_two,hpos.ne']
    ring_nf
    omega
  have hregBound :
      (∑ R : RegularIndex Q,(regularSeeds Q selected Γ R).card) ≤
        ContactKernelArithmetic6733Research.fixed (capOf Q) := by
    have hnest := residual_weight_nested Q
    have hfix := ContactKernelArithmetic6733Research.fixed_covers_identity_and_proper
      (capOf Q) hnest.2 hnest.1
    rw [originalFlag_eq_flagOfCap Q] at hreg
    have heq : fixedProfile = ContactKernelArithmetic6733Research.fixedProfile6733 := by
      rfl
    rw [heq] at hreg
    exact hreg.trans ((Nat.le_add_right _ _).trans hfix.1)
  exact hcover.trans (Nat.add_le_add hregBound hsingBound)
end
end ProximityPrize.SubmissionLower.ContactKernelFixedSelected6733Research
