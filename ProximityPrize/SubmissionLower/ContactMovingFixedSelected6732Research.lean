import ProximityPrize.SubmissionLower.ContactMovingFixedStage6732Research
import ProximityPrize.SubmissionLower.ContactFirstTailReducedProper6732Research
import ProximityPrize.SubmissionLower.ContactFirstTailIdentityIncidence6731Research
import ProximityPrize.SubmissionLower.ContactIdentityCurveProvider6731Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch

/-! Fixed regular-factor split between proper and identity first tails. -/
namespace ProximityPrize.SubmissionLower.ContactMovingFixedSelected6732Research

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
open ContactMovingFixedProfile6732Research ContactMovingFixedStage6732Research
open ContactFirstTailReducedProper6732Research ContactFirstTailIdentityIncidence6731Research
open ContactIdentityCurveProvider6731Research
open ContactProfileFixedSelectedCombinerResearch

noncomputable section
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 40000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _

private theorem geometric_identityDegree_pos
    {F : MvPolynomial (Fin 4) K} (g : GeometricFactor K F) :
    1 ≤ identityDegree fixedProfile 1167 43 9 (geometricCumulativeFlag K g) := by
  have hirr : Irreducible g.1 :=
    (surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).1
  have hp := irreducible_positive_surface_degree g.1 hirr
  have hflag := polynomialIn_surfaceCumulativeFlag g.1
  have h0 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 0
  have h1 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 1
  have h2 := degreeOf_le_flag_total g.1 (geometricCumulativeFlag K g) hflag 2
  have htotal : 0 < (geometricCumulativeFlag K g).zOnly+
      (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all := by omega
  unfold identityDegree ContactMovingOuterBudget6719Research.paddedCut
  simp only [ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    ContactFlagBezout6543Research.flagMixed,
    ContactFlagBezout6543Research.unitZFlag,
    ContactFlagBezout6543Research.unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  norm_num [fixedProfile, Profile.w]
  omega

theorem regular_factor_seed_bound
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hagreement : ∀ γ ∈ Γ, fixedProfile.agreements ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Γ R).card*fixedProfile.gap ≤
      factorLedger fixedProfile 1167 43 9 (regularCumulativeFlag Q R) := by
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
        fixedProfile.gap ≤ factorLedger fixedProfile 1167 43 9
          (geometricCumulativeFlag K g) := by
    intro g
    let S := fixedGeometricStage Q hQ hbox Hsupport selected Γ nodes x u0 u1
      hinj hdegree hnoPencil R g
    have hsub : geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g ⊆ Γ :=
      (geometricSeeds_subset K R.1 selected (regularSeeds Q selected Γ R) g).trans
        (regularSeeds_subset Q selected Γ R)
    have hnodesS : S.nodes.card=fixedProfile.n := by
      simpa [S, fixedGeometricStage, reflagResidualStage,
        regularGeometricResidualStageOfSupport, geometricResidualStageOfSupport] using hnodes
    have hagreementS : ∀ γ ∈ geometricSeeds K R.1 selected
        (regularSeeds Q selected Γ R) g,
        fixedProfile.agreements ≤ (S.agreementFiber γ).card := by
      intro γ hγ
      simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees, fixedGeometricStage,
        reflagResidualStage, regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using hagreement γ (hsub hγ)
    have hf := geometric_flag_caps Q hQ hbox Hsupport R g
    by_cases htail : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (fixedProfile.w+1))
    · have hsize : S.nodes.card=fixedProfile.agreements+fixedProfile.errors := by
        rw [hnodesS]
        rfl
      have hboxS : S.F ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
          fixedProfile.seedTotalCap fixedProfile.slopeCap := by
        simpa [S, fixedGeometricStage, reflagResidualStage,
          regularGeometricResidualStageOfSupport, geometricResidualStageOfSupport] using
          hRdata.2.2
      have hprovider := actual_identityCurveCountProvider S fixedProfile.agreements
        hsize hagreementS (by decide) htail fixedProfile.weightedCap
        fixedProfile.seedTotalCap fixedProfile.slopeCap (by decide) (by decide)
        (by decide) hboxS (by
          exact ⟨hf.2.1.trans_lt (by decide), hf.1.trans_lt (by decide),
            hf.2.2.trans_lt (by decide)⟩)
        (by
          have hc := hf
          norm_num [fixedProfile, fixedSupport, prime, Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
      change IdentityCurveCountProvider S
        (identityDegree fixedProfile 1167 43 9 (geometricCumulativeFlag K g)) at hprovider
      have hi := identity_surface_seed_bound S fixedProfile.agreements
        (identityDegree fixedProfile 1167 43 9 (geometricCumulativeFlag K g))
        hprovider hagreementS (by decide) (by rw [hnodesS]; decide)
        (geometric_identityDegree_pos g)
      have hi' : (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card*
          fixedProfile.gap ≤ (fixedProfile.n-fixedProfile.w)*(fixedProfile.errors+1)*
            identityDegree fixedProfile 1167 43 9 (geometricCumulativeFlag K g) := by
        rw [hnodesS] at hi
        simpa only [Profile.gap] using hi
      exact hi'.trans (by unfold factorLedger; omega)
    · have hproper := proper_firstTail_reduced_seed_bound (polynomialEmbedding_injective K)
        fixedProfile 1167 43 9 S hnodesS hagreementS (by decide) (by decide)
        fixed_degree_part_bound fixed_unit_part_bound htail
        (by
          exact ⟨hf.2.1.trans_lt (by decide), hf.1.trans_lt (by decide),
            hf.2.2.trans_lt (by decide)⟩)
        (by
          have hc := hf
          norm_num [fixedProfile, fixedSupport, prime, Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
        (by
          have hc := hf
          norm_num [fixedProfile, fixedSupport, prime, Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
        (by
          have hc := hf
          norm_num [fixedProfile, fixedSupport, prime, Profile.w,
            ContactMovingAgreementCertificate6719Research.support] at hc ⊢
          omega)
      exact hproper.trans (by unfold factorLedger; omega)
  calc
    _ ≤ (∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card)*
        fixedProfile.gap := Nat.mul_le_mul_right _ hcover
    _ = ∑ g : GeometricFactor K R.1,
        (geometricSeeds K R.1 selected (regularSeeds Q selected Γ R) g).card*
          fixedProfile.gap := by rw [Finset.sum_mul]
    _ ≤ ∑ g : GeometricFactor K R.1,
        factorLedger fixedProfile 1167 43 9 (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ ↦ hstage g)
    _ ≤ _ := by
      have hc := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact sum_factorLedger_le fixedProfile 1167 43 9 (geometricCumulativeFlag K)
        (originalCumulativeFlag R.1) hc.1 hc.2.1 hc.2.2

theorem fixed_selected_count_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) [CharP K prime]
    (hbox : Q ∈ globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport : ResidualSupportData fixedSupport Q)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = fixedProfile.n)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ fixedProfile.w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q=0)
    (hagreement : ∀ γ ∈ Γ, fixedProfile.agreements ≤
      (nodes.filter (fun i ↦ (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ fixedProfile.w fixedProfile.errors) :
    Γ.card ≤ ContactMovingParameters6732Research.fixedRegularCost+
      ContactMovingParameters6732Research.fixedSingularCost := by
  have h := global_count_le_regular_div_add_tight_countCap
    fixedProfile fixedTightProfile fixed_alignment Q hQ hbox
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    selected Γ nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
    (regularCumulativeFlag Q)
    (fun flag ↦ factorLedger fixedProfile 1167 43 9 flag*fixedProfile.gap)
    (regularNumerator := fixedFactorLedger*fixedProfile.gap)
    (fun count hcount ↦ by
      have hc := regularCumulativeFlag_budgets Q hQ Hsupport
      calc
        (∑ R, count R)*fixedProfile.gap^2 =
            (∑ R, count R*fixedProfile.gap^2) := by rw [Finset.sum_mul]
        _ ≤ ∑ R, factorLedger fixedProfile 1167 43 9
            (regularCumulativeFlag Q R)*fixedProfile.gap :=
          Finset.sum_le_sum (fun R _ ↦ hcount R)
        _ = (∑ R, factorLedger fixedProfile 1167 43 9
            (regularCumulativeFlag Q R))*fixedProfile.gap := by rw [Finset.sum_mul]
        _ ≤ fixedFactorLedger*fixedProfile.gap := Nat.mul_le_mul_right _
          (sum_factorLedger_le fixedProfile 1167 43 9 (regularCumulativeFlag Q)
            fixedFlag hc.1 hc.2.1 hc.2.2))
    (fun R ↦ by
      have hr := regular_factor_seed_bound Q hQ hbox Hsupport selected Γ nodes x u0 u1
        hinj hnodes hdegree hagreement hnoPencil R
      have hm := Nat.mul_le_mul_right fixedProfile.gap hr
      simpa [pow_two, mul_assoc] using hm)
  exact h.trans fixed_inclusive_cost_le

end
end ProximityPrize.SubmissionLower.ContactMovingFixedSelected6732Research
