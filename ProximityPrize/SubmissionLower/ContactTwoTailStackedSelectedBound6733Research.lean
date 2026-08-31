import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactTwoTailStackedInterpolation6733Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactTwoTailStackedBoxTransport6733Research
import ProximityPrize.SubmissionLower.ContactTwoTailSecondResidualCell6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailStackedSelectedBound6733Research
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactTwoTailParameters6733Research
open ContactStackedGCDCover6670Research ContactStackedSeedPartition6670Research
open ContactTwoTailResidualCells6733Research
open ContactTwoTailStackedBoxTransport6733Research
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid GlobalPoly:=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def FixedCellCountProvider6733:Prop:=
  ∀ (Q:GlobalPoly),Q≠0 →
    Q∈globalCoefficientBox IRSProfile.Field (41*agreements) w 1242 11 →
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
    (provider:FixedCellCountProvider6733)
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
      (41*agreements) w 1242 11:=by
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
theorem selectedNoLargePencilBound6733_of_fixedProvider
    (provider:FixedCellCountProvider6733):
    SelectedNoLargePencilBound IRSProfile.domain
      131071 80092 274980727256461038:=by
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
    ContactTwoTailStackedInterpolation6733Research.exists_interpolants_with_recursive_cover
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
    change (firstResidualSeeds selected seeds QA QB).card < 790506015947499
    exact hfirstRaw
  have hsecond:(secondResidualSeeds selected seeds QA QB QC).card <
      secondResidualCeiling:=by
    change (secondResidualSeeds selected seeds QA QB QC).card < 1203336772963221
    exact hsecondRaw
  have hfixed:=fixedSeeds_card_le_of_provider provider QA QB QC hQA hQB hQC
    hboxA hboxB hboxC hflagB selected seeds (U 0) (U 1)
    hdegree hagreement hno
  have hfinal:=selected_card_le_mcaBudget_of_cell_bounds
    selected seeds QA QB QC hfirst hsecond hfixed
  change seeds.card ≤ 274980727256461038 at hfinal
  exact hfinal
end
end ProximityPrize.SubmissionLower.ContactTwoTailStackedSelectedBound6733Research
