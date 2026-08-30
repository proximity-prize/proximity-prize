import ProximityPrize.SubmissionLower.GW

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedSelectedBound6735Research
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactTwoTailParameters6735Research
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactTwoTailResidualCells6735Research
open ContactTwoTailStackedBoxTransport6735Research
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def FixedCellCountProvider6735:Prop:=
  ∀ (Q:GlobalPoly),Q≠0 →
    Q∈globalCoefficientBox IRSProfile.Field (43*agreements) w 1394 12 →
    ResidualSupportData fixedSupport Q →
    ∀ (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
      (Delta:Finset IRSProfile.Field)
      (u0 u1:IRSProfile.Index → IRSProfile.Field),
      (∀ gamma∈Delta,
        specialization IRSProfile.Field (selected gamma) gamma Q=0) →
      (∀ gamma∈Delta,(selected gamma).natDegree ≤ w) →
      (∀ gamma∈Delta,agreements ≤
        ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
          (selected gamma).eval (IRSProfile.domain i)=
            u0 i+gamma*u1 i)).card) →
      NoLargeSelectedPencil selected Delta w errors →
      Delta.card ≤ fixedCost
theorem selected_card_le_mcaBudget_of_cell_bounds
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
    (hfirst:(firstResidualSeeds selected Gamma QA QB).card <
      firstResidualCeiling)
    (hsecond:(secondResidualSeeds selected Gamma QA QB QC).card <
      secondResidualCeiling)
    (hfixed:(fixedSeeds selected Gamma QA QB QC).card ≤ fixedCost):
    Gamma.card ≤ mcaBudget:=by
  have hpartition:Gamma.card=
      (firstResidualSeeds selected Gamma QA QB).card+
      (secondResidualSeeds selected Gamma QA QB QC).card+
      (fixedSeeds selected Gamma QA QB QC).card:=
    (partition_card selected Gamma QA QB QC).symm
  have hbudget:=cell_budget_strict
  omega
theorem selected_recursive_cover
    (U:Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds:Finset IRSProfile.Field)
    (A:IRSProfile.Field → Finset IRSProfile.Index)
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (QA QB QC:GlobalPoly)
    (huniversal:∀ gamma P (support:Finset IRSProfile.Index),
      P.natDegree ≤ w → agreements ≤ support.card →
      (∀ i∈support,
        P.eval (IRSProfile.domain i)=U 0 i+gamma*U 1 i) →
      RecursiveSpecializationBranch P gamma QA QB QC)
    (hdegree:∀ gamma∈seeds,(selected gamma).natDegree ≤ w)
    (hcard:∀ gamma∈seeds,
      Fintype.card IRSProfile.Index-errors ≤ (A gamma).card)
    (hvalues:∀ gamma∈seeds,∀ i∈A gamma,
      (selected gamma).eval (IRSProfile.domain i)=U 0 i+gamma*U 1 i):
    ∀ gamma∈seeds,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC:=by
  intro gamma hgamma
  apply huniversal gamma (selected gamma) (A gamma)
  · exact hdegree gamma hgamma
  · have hh:=hcard gamma hgamma
    norm_num [IRSProfile.Index,errors,n,agreements] at hh ⊢
    exact hh
  · exact hvalues gamma hgamma
theorem selected_full_domain_agreement
    (U:Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds:Finset IRSProfile.Field)
    (A:IRSProfile.Field → Finset IRSProfile.Index)
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (hcard:∀ gamma∈seeds,
      Fintype.card IRSProfile.Index-errors ≤ (A gamma).card)
    (hvalues:∀ gamma∈seeds,∀ i∈A gamma,
      (selected gamma).eval (IRSProfile.domain i)=U 0 i+gamma*U 1 i):
    ∀ gamma∈seeds,agreements ≤
      ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          U 0 i+gamma*U 1 i)).card:=by
  intro gamma hgamma
  have hsub:A gamma ⊆
      (Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          U 0 i+gamma*U 1 i):=by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvalues gamma hgamma i hi⟩
  have hsize:=(hcard gamma hgamma).trans (Finset.card_le_card hsub)
  norm_num [IRSProfile.Index,errors,n,agreements] at hsize ⊢
  exact hsize
theorem fixedSeeds_card_le_of_provider
    (provider:FixedCellCountProvider6735)
    (QA QB QC:GlobalPoly) (hQA:QA≠0) (hQB:QB≠0) (hQC:QC≠0)
    (hboxA:QA∈globalCoefficientBox IRSProfile.Field
      profileA.weightedCap w profileA.totalCap profileA.slopeCap)
    (hboxB:QB∈globalCoefficientBox IRSProfile.Field
      profileB.weightedCap w profileB.totalCap profileB.slopeCap)
    (hboxC:QC∈globalCoefficientBox IRSProfile.Field
      profileC.weightedCap w profileC.totalCap profileC.slopeCap)
    (hflagB:QB∈ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field profileB.weightedCap w profileB.totalCap profileB.slopeCap)
    (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma:Finset IRSProfile.Field)
    (u0 u1:IRSProfile.Index → IRSProfile.Field)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
    (hagreement:∀ gamma∈Gamma,agreements ≤
      ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card)
    (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
    (fixedSeeds selected Gamma QA QB QC).card ≤ fixedCost:=by
  let Q:=gcd123 QA QB QC
  let Delta:=fixedSeeds selected Gamma QA QB QC
  have hQ:Q≠0:=by
    simpa [Q] using ContactStackedBoxTransport6656Research.gcd123_ne_zero
      (B:=QB) (C:=QC) hQA
  have hbox12:=gcd12_mem_meet_box QA QB hQA hQB hboxA hboxB
  have hQbox:Q∈globalCoefficientBox IRSProfile.Field
      (43*agreements) w 1394 12:=by
    simpa [Q] using gcd123_mem_meet_box QA QB QC hQA hQC hbox12 hboxC
  have hsupport:=gcd123_support_of_flagB
    QA QB QC hQA hQB hQC hboxA hboxB hboxC hflagB
  have hsub:Delta ⊆ Gamma:=by
    simpa [Delta] using fixedSeeds_subset selected Gamma QA QB QC
  have hsolution:∀ gamma∈Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q=0:=by
    simpa [Q,Delta] using fixedSeeds_vanish selected Gamma QA QB QC
  have hdegreeDelta:∀ gamma∈Delta,(selected gamma).natDegree ≤ w:=
    fun gamma hgamma↦hdegree gamma (hsub hgamma)
  have hagreementDelta:∀ gamma∈Delta,agreements ≤
      ((Finset.univ:Finset IRSProfile.Index).filter (fun i↦
        (selected gamma).eval (IRSProfile.domain i)=
          u0 i+gamma*u1 i)).card:=
    fun gamma hgamma↦hagreement gamma (hsub hgamma)
  have hnoDelta:NoLargeSelectedPencil selected Delta w errors:=
    noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  simpa [Delta] using provider Q hQ hQbox hsupport selected Delta u0 u1
    hsolution hdegreeDelta hagreementDelta hnoDelta
theorem selectedNoLargePencilBound6735_of_fixedProvider
    (provider:FixedCellCountProvider6735):
    SelectedNoLargePencilBound IRSProfile.domain
      131071 80161 274980727143946195:=by
  intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
  have hdegree:∀ gamma∈seeds,(selected gamma).natDegree ≤ w:=by
    simpa [w] using hdegreeRaw
  have hcard:∀ gamma∈seeds,
      Fintype.card IRSProfile.Index-errors ≤ (A gamma).card:=by
    simpa [errors,n,agreements] using hcardRaw
  have hagreement:=selected_full_domain_agreement U seeds A selected hcard hvalues
  have hno:NoLargeSelectedPencil selected seeds w errors:=by
    intro P0 P1 hP0 hP1
    have hh:=hnoRaw P0 P1 (by simpa [w] using hP0) (by simpa [w] using hP1)
    convert hh using 1
    · apply congrArg Finset.card
      ext gamma
      simp [pencilSeeds]
    · norm_num [errors,n,agreements]
  obtain ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,hall⟩:=
    ContactTwoTailStackedInterpolation6735Research.exists_interpolants_with_recursive_cover
      (U 0) (U 1)
  have hcover:=selected_recursive_cover U seeds A selected QA QB QC
    hall hdegree hcard hvalues
  have hfirstRaw:=firstResidualCell_count_lt QA QB QC hQA hQB hboxA hboxB
    selected seeds (U 0) (U 1) hcover hdegree hagreement hno
  have hsecondRaw:=secondResidualCell_count_lt QA QB QC hQA hQB hQC
    hboxA hboxB hboxC selected seeds (U 0) (U 1)
    hcover hdegree hagreement hno
  have hfirst:(firstResidualSeeds selected seeds QA QB).card <
      firstResidualCeiling:=by
    change (firstResidualSeeds selected seeds QA QB).card < 1393009602951623
    exact hfirstRaw
  have hsecond:(secondResidualSeeds selected seeds QA QB QC).card <
      secondResidualCeiling:=by
    change (secondResidualSeeds selected seeds QA QB QC).card < 160719217478267
    exact hsecondRaw
  have hfixed:=fixedSeeds_card_le_of_provider provider QA QB QC hQA hQB hQC
    hboxA hboxB hboxC hflagB selected seeds (U 0) (U 1)
    hdegree hagreement hno
  have hfinal:=selected_card_le_mcaBudget_of_cell_bounds
    selected seeds QA QB QC hfirst hsecond hfixed
  change seeds.card ≤ 274980727143946195 at hfinal
  exact hfinal
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedSelectedBound6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6735Research
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
open ContactTwoTailParameters6735Research
open ContactTwoTailFixedStage6735Research
open ContactTwoTailIdentityStage6735Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev fixedProfile:=ContactTwoTailFixedProvider6735Research.fixedProfile
abbrev fixedSupport:=ContactTwoTailFixedProvider6735Research.fixedSupport
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def fixedTightProfile:TightParameters:=
  ⟨n,w,agreements,43*agreements,1394,12⟩
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
    (S:ContactProperDelayedTailCertificate6735Research.Stage
      K I Gamma IRSProfile.domain prime flag),
    ¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1) →
    S.nodes.card=agreements+errors →
    (∀ gamma∈Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F∈globalCoefficientBox K (43*agreements) w 1394 12 →
    (flag.all ≤ 12∧flag.yz+flag.all ≤ 59∧
      flag.zOnly+flag.yz+flag.all ≤ 1394) →
    Gamma.card ≤ hybridStageCost flag
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
      hybridStageCost (regularCumulativeFlag Q R):=by
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
        hybridStageCost (geometricCumulativeFlag K g):=by
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
    have hboxS:S.F∈globalCoefficientBox K (43*agreements) w 1394 12:=by
      change R.1∈globalCoefficientBox K (43*agreements) w 1394 12
      simpa [fixedProfile,
        ContactTwoTailFixedProvider6735Research.fixedProfile,
        agreements,errors,n,w] using hRdata.2.2
    by_cases htail:S.G∣
        globalTailCut (polynomialEmbedding K) S.F (w+1)
    · exact identity_stage_card_le S htail hnodesS hagreementS hboxS hflag
    · exact proper S htail hnodesS hagreementS hboxS hflag
  calc
    (regularSeeds Q selected Gamma R).card ≤
        ∑ g:GeometricFactor K R.1,
          (geometricSeeds K R.1 selected
            (regularSeeds Q selected Gamma R) g).card:=hcover
    _ ≤ ∑ g:GeometricFactor K R.1,
        hybridStageCost (geometricCumulativeFlag K g):=
      Finset.sum_le_sum (fun g _↦hstage g)
    _ ≤ hybridStageCost (originalCumulativeFlag R.1):=by
      have hc:=geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
      unfold hybridStageCost
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      exact Nat.add_le_add
        (sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
          (originalCumulativeFlag R.1) _ _ hc.1 hc.2.1 hc.2.2)
        (Nat.mul_le_mul_left _
          (sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
            (originalCumulativeFlag R.1) _ _ hc.1 hc.2.1 hc.2.2))
theorem fixedCellCountProvider_of_proper
    (proper:ProperStageProvider6733):
    ContactTwoTailStackedSelectedBound6735Research.FixedCellCountProvider6735:=by
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
    (fun f↦hybridStageCost f*gap^2)
    (fun count hcount↦by
      have hc:=regularCumulativeFlag_budgets Q hQ Hsupport
      calc
        (∑ R,count R)*gap^2=∑ R,count R*gap^2:=by
          rw [Finset.sum_mul]
        _ ≤ ∑ R,hybridStageCost (regularCumulativeFlag Q R)*gap^2:=
          Finset.sum_le_sum (fun R _↦hcount R)
        _=(∑ R,hybridStageCost (regularCumulativeFlag Q R))*gap^2:=by
          rw [Finset.sum_mul]
        _ ≤ fixedRegularCost*gap^2:=Nat.mul_le_mul_right _
          (by
            change (∑ R,hybridStageCost (regularCumulativeFlag Q R)) ≤
              hybridStageCost fixedFlag
            unfold hybridStageCost
            rw [Finset.sum_add_distrib,←Finset.mul_sum]
            exact Nat.add_le_add
              (sum_flagMixed_le_of_cumulative (regularCumulativeFlag Q)
                fixedFlag _ _
                (hc.1.trans_eq (by decide))
                (hc.2.1.trans_eq (by decide))
                (hc.2.2.trans_eq (by decide)))
              (Nat.mul_le_mul_left _
                (sum_flagMixed_le_of_cumulative (regularCumulativeFlag Q)
                  fixedFlag _ _
                  (hc.1.trans_eq (by decide))
                  (hc.2.1.trans_eq (by decide))
                  (hc.2.2.trans_eq (by decide))))))
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
end ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6735Research
end
