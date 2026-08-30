import ProximityPrize.SubmissionLower.ContactTwoTailFixedStage6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailStackedSelectedBound6733Research
import ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6733Research
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactFlagBezout6543Research
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research ContactResidualSupportParametersResearch
open ContactIdentityResidualIterationResearch ContactGCDCumulativeFlagsResearch
open ContactFactoredFlagCount6676Research ContactGeometricFactorCover
open ContactRobustFixedMeet6656Research
open ContactProfileFixedSelectedCombinerResearch
open ContactTightSingularLedgerResearch
open ContactDelayedTailMultiplicityProvider6732Research
open ContactTwoTailParameters6733Research
open ContactTwoTailFixedStage6733Research
open ContactTwoTailIdentityStage6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev fixedProfile:=ContactTwoTailFixedProvider6732Research.fixedProfile
abbrev fixedSupport:=ContactTwoTailFixedProvider6732Research.fixedSupport
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def fixedTightProfile:TightParameters:=
  ⟨n,w,agreements,41*agreements,1242,11⟩
def fixedAlignment:FixedParameterAlignment fixedProfile fixedTightProfile where
  n:=by decide
  w:=by decide
  agreements:=by decide
  weightedCap:=by decide
  seedTotalCap:=by decide
  slopeCap:=by decide
theorem fixed_numeric_bridge:
    fixedTightProfile.countCap+1=fixedSingularCost∧
      fixedProfile.gap=gap∧
      (fixedRegularCost*gap^2)/gap^2=fixedRegularCost:=by
  refine ⟨?_,?_,?_⟩
  · decide
  · decide
  · exact Nat.mul_div_left _ (pow_pos (by decide:0 < gap) 2)
def ProperStageProvider6733:Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree}
    (S:ContactProperDelayedTailCertificate6732Research.Stage
      K I Gamma IRSProfile.domain prime flag),
    ¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1) →
    S.nodes.card=agreements+errors →
    (∀ gamma∈Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F∈globalCoefficientBox K (41*agreements) w 1242 11 →
    (flag.all ≤ 11∧flag.yz+flag.all ≤ 56∧
      flag.zOnly+flag.yz+flag.all ≤ 1242) →
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1:=tailFlag (w+1))
      (tailFlag2:=tailFlag (w+2)) S)
theorem regular_factor_seed_bound
    (proper:ProperStageProvider6733)
    (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hbox:Q∈globalCoefficientBox K fixedProfile.weightedCap fixedProfile.w
      fixedProfile.seedTotalCap fixedProfile.slopeCap)
    (Hsupport:ResidualSupportData fixedSupport Q)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (u0 u1:I → K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,agreements ≤
      ((Finset.univ:Finset I).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
    (R:RegularIndex Q):
    (regularSeeds Q selected Gamma R).card ≤
      flagMixed (regularCumulativeFlag Q R)
        (tailFlag (w+1)) (tailFlag (w+2)):=by
  letI:CharP (GenericField K) prime:=genericField_charP K prime
  have hRdata:=directFactor_data Q R.1 hQ fixedProfile.weightedCap
    fixedProfile.w fixedProfile.seedTotalCap fixedProfile.slopeCap hbox R.2
  have hsolutions:∀ gamma∈regularSeeds Q selected Gamma R,
      specialization K (selected gamma) gamma R.1=0:=by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2.1
  have hcover:=card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
    (regularSeeds Q selected Gamma R) hsolutions
  have hstage:∀ g:GeometricFactor K R.1,
      (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
        flagMixed (geometricCumulativeFlag K g)
          (tailFlag (w+1)) (tailFlag (w+2)):=by
    intro g
    let S:=fixedGeometricStage Q hQ hbox Hsupport selected Gamma u0 u1
      hdegree hnoPencil R g
    have hsub:geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g ⊆ Gamma:=
      (geometricSeeds_subset K R.1 selected
        (regularSeeds Q selected Gamma R) g).trans
          (regularSeeds_subset Q selected Gamma R)
    have hnodesS:S.nodes.card=agreements+errors:=by
      change (Finset.univ:Finset I).card=agreements+errors
      norm_num [I,agreements,errors,n]
    have hagreementS:∀ gamma∈geometricSeeds K R.1 selected
        (regularSeeds Q selected Gamma R) g,
        agreements ≤ (S.agreementFiber gamma).card:=by
      intro gamma hgamma
      simpa [S,ResidualStage.agreementFiber,ResidualStage.Agrees,
        fixedGeometricStage,reflagResidualStage,
        regularGeometricResidualStageOfSupport,
        geometricResidualStageOfSupport] using
          hagreement gamma (hsub hgamma)
    have hflag:=geometric_flag_caps Q hQ hbox Hsupport R g
    have hboxS:S.F∈globalCoefficientBox K (41*agreements) w 1242 11:=by
      change R.1∈globalCoefficientBox K (41*agreements) w 1242 11
      simpa [fixedProfile,
        ContactTwoTailFixedProvider6732Research.fixedProfile,
        agreements,errors,n,w] using hRdata.2.2
    by_cases htail:S.G∣
        globalTailCut (polynomialEmbedding K) S.F (w+1)
    · exact identity_stage_card_le S htail hnodesS hagreementS hboxS hflag
    · exact stage_card_le_flagMixed S
        (proper S htail hnodesS hagreementS hboxS hflag).some
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        flagMixed (geometricCumulativeFlag K g)
          (tailFlag (w+1)) (tailFlag (w+2)):=
      Finset.sum_le_sum (fun g _↦hstage g)
    _ ≤ flagMixed (originalCumulativeFlag R.1)
        (tailFlag (w+1)) (tailFlag (w+2)):=by
      have hc:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      exact sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
        (originalCumulativeFlag R.1) _ _ hc.1 hc.2.1 hc.2.2
theorem fixedCellCountProvider_of_proper
    (proper:ProperStageProvider6733):
    ContactTwoTailStackedSelectedBound6733Research.FixedCellCountProvider6733:=by
  intro Q hQ hbox Hsupport selected Gamma u0 u1 hsolution hdegree
    hagreement hnoPencil
  let nodes:Finset I:=Finset.univ
  have hinj:Set.InjOn IRSProfile.domain nodes:=
    IRSProfile.domain.injective.injOn
  have hnodes:nodes.card=fixedProfile.n:=by
    change Fintype.card I=262144
    norm_num [I,IRSProfile.Index]
  have h:=global_count_le_regular_div_add_tight_countCap
    fixedProfile fixedTightProfile fixedAlignment
    (prime:=prime) (regularNumerator:=fixedRegularCost*gap^2)
    Q hQ hbox
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) selected Gamma nodes IRSProfile.domain
    u0 u1 hinj hnodes hdegree
    hsolution hagreement hnoPencil (regularCumulativeFlag Q)
    (fun f↦flagMixed f (tailFlag (w+1)) (tailFlag (w+2))*gap^2)
    (fun count hcount↦by
      have hc:=regularCumulativeFlag_budgets Q hQ Hsupport
      calc
        (∑ R,count R)*gap^2=∑ R,count R*gap^2:=by
          rw [Finset.sum_mul]
        _ ≤ ∑ R,flagMixed (regularCumulativeFlag Q R)
              (tailFlag (w+1)) (tailFlag (w+2))*gap^2:=
          Finset.sum_le_sum (fun R _↦hcount R)
        _=(∑ R,flagMixed (regularCumulativeFlag Q R)
              (tailFlag (w+1)) (tailFlag (w+2)))*gap^2:=by
          rw [Finset.sum_mul]
        _ ≤ fixedRegularCost*gap^2:=Nat.mul_le_mul_right _
          (by
            change (∑ R,flagMixed (regularCumulativeFlag Q R)
              (tailFlag (w+1)) (tailFlag (w+2))) ≤
                flagMixed fixedFlag (tailFlag (w+1)) (tailFlag (w+2))
            exact sum_flagMixed_le_of_cumulative (regularCumulativeFlag Q)
              fixedFlag _ _
              (hc.1.trans_eq (by decide))
              (hc.2.1.trans_eq (by decide))
              (hc.2.2.trans_eq (by decide))))
    (fun R↦by
      have hr:=regular_factor_seed_bound proper Q hQ hbox Hsupport selected
        Gamma u0 u1 hdegree hagreement hnoPencil R
      rw [show fixedProfile.gap=gap by decide]
      exact Nat.mul_le_mul_right (gap^2) hr)
  have hbridge:=fixed_numeric_bridge
  calc
    Gamma.card ≤ fixedRegularCost+fixedTightProfile.countCap:=by
      simpa only [hbridge.2.1,hbridge.2.2] using h
    _ ≤ fixedRegularCost+fixedSingularCost:=
      Nat.add_le_add_left (by omega) fixedRegularCost
end
end ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6733Research
