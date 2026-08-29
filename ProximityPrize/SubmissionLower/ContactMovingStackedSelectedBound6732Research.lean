import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactMovingStackedBoxTransport6732Research
import ProximityPrize.SubmissionLower.ContactMovingStackedResidualCells6732Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
/-! .





 -/
namespace ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6732Research
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactRecursiveGCDResearch
open ContactMovingParameters6732Research
attribute [local simp] n errors agreements
open ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactMovingStackedResidualCells6732Research
open ContactMovingParameters6732Research
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
/-- .

 -/
def FixedCellCountProvider6732 : Prop :=
  ∀ (Q : GlobalPoly), Q ≠ 0 →
    Q ∈ globalCoefficientBox IRSProfile.Field (40 * agreements) w 1222 11 →
    ResidualSupportData ContactMovingStackedBoxTransport6732Research.fixedSupport Q →
    ∀ (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
      (Delta : Finset IRSProfile.Field)
      (u0 u1 : IRSProfile.Index → IRSProfile.Field),
      (∀ gamma ∈ Delta,
        specialization IRSProfile.Field (selected gamma) gamma Q = 0) →
      (∀ gamma ∈ Delta, (selected gamma).natDegree ≤ w) →
      (∀ gamma ∈ Delta, agreements ≤
        ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card) →
      NoLargeSelectedPencil selected Delta w errors →
      Delta.card ≤ fixedCost
/-- . -/
theorem selected_card_le_mcaBudget_of_cell_bounds
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field) (QA QB QC : GlobalPoly)
    (hfirst : (firstResidualSeeds selected Gamma QA QB).card <
      firstResidualCeiling)
    (hsecond : (secondResidualSeeds selected Gamma QA QB QC).card <
      secondResidualCeiling)
    (hfixed : (fixedSeeds selected Gamma QA QB QC).card ≤ fixedCost) :
    Gamma.card ≤ mcaBudget := by
  have hpartition : Gamma.card =
      (firstResidualSeeds selected Gamma QA QB).card +
        (secondResidualSeeds selected Gamma QA QB QC).card +
        (fixedSeeds selected Gamma QA QB QC).card :=
    (partition_card selected Gamma QA QB QC).symm
  have hlt := total_lt_mcaBudget Gamma.card
    (firstResidualSeeds selected Gamma QA QB).card
    (secondResidualSeeds selected Gamma QA QB QC).card
    (fixedSeeds selected Gamma QA QB QC).card
    hpartition hfirst hsecond hfixed
  omega
/-- .
 -/
theorem selected_recursive_cover
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (QA QB QC : GlobalPoly)
    (huniversal : ∀ (gamma : IRSProfile.Field)
      (P : Polynomial IRSProfile.Field) (support : Finset IRSProfile.Index),
      P.natDegree ≤ w → agreements ≤ support.card →
      (∀ i ∈ support,
        P.eval (IRSProfile.domain i) = U 0 i + gamma * U 1 i) →
      RecursiveSpecializationBranch P gamma QA QB QC)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hcard : ∀ gamma ∈ seeds,
      Fintype.card IRSProfile.Index - errors ≤ (A gamma).card)
    (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (IRSProfile.domain i) =
        U 0 i + gamma * U 1 i) :
    ∀ gamma ∈ seeds,
      RecursiveSpecializationBranch (selected gamma) gamma QA QB QC := by
  intro gamma hgamma
  apply huniversal gamma (selected gamma) (A gamma)
  · exact hdegree gamma hgamma
  · have hh := hcard gamma hgamma
    norm_num [IRSProfile.Index, errors, n, agreements] at hh ⊢
    exact hh
  · exact hvalues gamma hgamma
/-- .
 -/
theorem selected_full_domain_agreement
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hcard : ∀ gamma ∈ seeds,
      Fintype.card IRSProfile.Index - errors ≤ (A gamma).card)
    (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ A gamma,
      (selected gamma).eval (IRSProfile.domain i) =
        U 0 i + gamma * U 1 i) :
    ∀ gamma ∈ seeds, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
  intro gamma hgamma
  have hA : A gamma ⊆
      (Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i) := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hgamma i hi⟩
  have hsize := (hcard gamma hgamma).trans (Finset.card_le_card hA)
  norm_num [IRSProfile.Index, errors, n, agreements] at hsize ⊢
  exact hsize
/-- .
 -/
theorem fixedSeeds_card_le_of_provider
    (hfixedProvider : FixedCellCountProvider6732)
    (QA QB QC : GlobalPoly) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hQC : QC ≠ 0)
    (hboxA : QA ∈ globalCoefficientBox IRSProfile.Field
      (43 * agreements) w 38583 11)
    (hboxB : QB ∈ globalCoefficientBox IRSProfile.Field
      (81 * agreements) w 1222 25)
    (hboxC : QC ∈ globalCoefficientBox IRSProfile.Field
      (40 * agreements) w 91386 12)
    (hflagB : QB ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field (81 * agreements) w 1222 25)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    (fixedSeeds selected Gamma QA QB QC).card ≤ fixedCost := by
  let Q := gcd123 QA QB QC
  let Delta := fixedSeeds selected Gamma QA QB QC
  have hQ : Q ≠ 0 := by
    simpa [Q] using
      ContactStackedBoxTransport6656Research.gcd123_ne_zero
        (B := QB) (C := QC) hQA
  have hbox12 :=
    ContactMovingStackedBoxTransport6732Research.gcd12_mem_meet_box
      QA QB hQA hQB hboxA hboxB
  have hQbox : Q ∈ globalCoefficientBox IRSProfile.Field
      (40 * agreements) w 1222 11 := by
    simpa [Q] using
      ContactMovingStackedBoxTransport6732Research.gcd123_mem_meet_box
        QA QB QC hQA hQC hbox12 hboxC
  have hQsupport := ContactMovingStackedBoxTransport6732Research.gcd123_support_of_flagB
    QA QB QC hQA hQB hQC hboxA hboxB hboxC hflagB
  have hsub : Delta ⊆ Gamma := by
    simpa [Delta] using fixedSeeds_subset selected Gamma QA QB QC
  have hsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0 := by
    simpa [Q, Delta] using fixedSeeds_vanish selected Gamma QA QB QC
  have hdegreeDelta : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ w := by
    intro gamma hgamma
    exact hdegree gamma (hsub hgamma)
  have hagreementDelta : ∀ gamma ∈ Delta, agreements ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card := by
    intro gamma hgamma
    exact hagreement gamma (hsub hgamma)
  have hnoPencilDelta : NoLargeSelectedPencil selected Delta w errors :=
    noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
  simpa [Delta] using hfixedProvider Q hQ hQbox hQsupport selected Delta u0 u1
    hsolution hdegreeDelta hagreementDelta hnoPencilDelta
/-- .
 -/
theorem selectedNoLargePencilBound6732_of_fixedProvider
    (hfixedProvider : FixedCellCountProvider6732) :
    SelectedNoLargePencilBound IRSProfile.domain
      131071 80082 274980727111395087 := by
  intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
  have hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ w := by
    simpa [w] using hdegreeRaw
  have hcard : ∀ gamma ∈ seeds,
      Fintype.card IRSProfile.Index - errors ≤ (A gamma).card := by
    simpa [errors, n, agreements] using hcardRaw
  have hagreement := selected_full_domain_agreement U seeds A selected
    hcard hvalues
  have hno : NoLargeSelectedPencil selected seeds w errors := by
    intro P0 P1 hP0 hP1
    have hh := hnoRaw P0 P1 (by simpa [w] using hP0)
      (by simpa [w] using hP1)
    convert hh using 1
    · apply congrArg Finset.card
      ext gamma
      simp [pencilSeeds]
    · norm_num [errors, n, agreements]
  obtain ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, hflagB,
      huniversal⟩ :=
    ContactMovingStackedInterpolation6732Research.exists_stacked_interpolants_with_recursive_cover (U 0) (U 1)
  have hcover := selected_recursive_cover U seeds A selected QA QB QC
    huniversal hdegree hcard hvalues
  have hfirstRaw := firstResidualCell_count_lt QA QB QC hQA hQB hboxA hboxB
    selected seeds (U 0) (U 1) hcover hdegree hagreement hno
  have hsecondRaw := secondResidualCell_count_lt QA QB QC hQA hQB hQC
    hboxA hboxB hboxC selected seeds (U 0) (U 1) hcover hdegree hagreement hno
  have hfirst : (firstResidualSeeds selected seeds QA QB).card <
      firstResidualCeiling := by
    simpa only [firstResidualCeiling, six_cells_exact.2.2.1,
      six_cells_exact.2.2.2.1] using hfirstRaw
  have hsecond : (secondResidualSeeds selected seeds QA QB QC).card <
      secondResidualCeiling := by
    simpa only [secondResidualCeiling, six_cells_exact.2.2.2.2.1,
      six_cells_exact.2.2.2.2.2] using hsecondRaw
  have hfixed := fixedSeeds_card_le_of_provider hfixedProvider
    QA QB QC hQA hQB hQC hboxA hboxB hboxC hflagB selected seeds
    (U 0) (U 1) hdegree hagreement hno
  simpa only [base_values.2.2.2.1] using
    selected_card_le_mcaBudget_of_cell_bounds selected seeds QA QB QC
      hfirst hsecond hfixed

end
end ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6732Research
