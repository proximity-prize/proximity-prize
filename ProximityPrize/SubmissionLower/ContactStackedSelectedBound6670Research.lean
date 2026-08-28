import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactStackedInterpolation6670Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
import ProximityPrize.SubmissionLower.ContactStackedResidualCells6670Research
import ProximityPrize.SubmissionLower.ContactStackedPromotedArithmetic6670Research

/-!
# Selected-family composition for the stacked 67.11 route

The three contact interpolants, recursive GCD cover, exact seed partition,
both residual-cell bounds, and promoted-budget arithmetic are all concrete.
The sole remaining premise is a count bound for an arbitrary nonzero fixed
meet polynomial in the target box, stated directly on its selected seed cell.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactRecursiveGCDResearch
open ContactStackedParameters6670Research
open ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactStackedResidualCells6670Research
open ContactStackedPromotedArithmetic6670Research
open ContactResidualSupportParametersResearch

noncomputable section

set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

/-- The narrow fixed-cell seam.  It speaks only about the final meet
polynomial and the selected cell on which it specializes to zero; the three
parent interpolants and recursive cover are deliberately absent. -/
def FixedCellCountProvider6670 : Prop :=
  ∀ (Q : GlobalPoly), Q ≠ 0 →
    Q ∈ globalCoefficientBox IRSProfile.Field (35 * agreements) w 900 10 →
    ResidualSupportData ContactFixedMeetProfile6670Research.fixedSupport Q →
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

/-- Pure final addition after the exact disjoint partition. -/
theorem selected_card_le_promotedBudget_of_cell_bounds
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Gamma : Finset IRSProfile.Field) (QA QB QC : GlobalPoly)
    (hfirst : (firstResidualSeeds selected Gamma QA QB).card <
      firstResidualCeiling)
    (hsecond : (secondResidualSeeds selected Gamma QA QB QC).card <
      secondResidualCeiling)
    (hfixed : (fixedSeeds selected Gamma QA QB QC).card ≤ fixedCost) :
    Gamma.card ≤ promotedBudget := by
  have hpartition : Gamma.card =
      (firstResidualSeeds selected Gamma QA QB).card +
        (secondResidualSeeds selected Gamma QA QB QC).card +
        (fixedSeeds selected Gamma QA QB QC).card :=
    (partition_card selected Gamma QA QB QC).symm
  have hlt := total_lt_promotedBudget Gamma.card
    (firstResidualSeeds selected Gamma QA QB).card
    (secondResidualSeeds selected Gamma QA QB QC).card
    (fixedSeeds selected Gamma QA QB QC).card
    hpartition hfirst hsecond hfixed
  omega

/-- Restrict the universal interpolation cover to the supplied selected
family and its original agreement supports. -/
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

/-- The caller's support embeds in the full-domain agreement filter used by
all three cell providers. -/
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
  have hsub : A gamma ⊆
      (Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvalues gamma hgamma i hi
  have hh := (hcard gamma hgamma).trans (Finset.card_le_card hsub)
  norm_num [IRSProfile.Index, errors, n, agreements] at hh ⊢
  exact hh

/-- Concrete selected-family bound for any supplied fixed-cell count
provider. -/
theorem selectedNoLargePencilBound_of_fixedCellCountProvider6670
    (hfixedProvider : FixedCellCountProvider6670) :
    SelectedNoLargePencilBound IRSProfile.domain
      131071 79876 274980727411395087 := by
  intro U seeds A selected hdegreeRaw hcardRaw hvalues hnoRaw
  have hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ w := by
    intro gamma hg
    have hd := hdegreeRaw gamma hg
    norm_num [w] at hd ⊢
    exact hd
  have hcard : ∀ gamma ∈ seeds,
      Fintype.card IRSProfile.Index - errors ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcardRaw gamma hg
    norm_num [IRSProfile.Index, errors] at hc ⊢
    exact hc
  have hnoPencil : NoLargeSelectedPencil selected seeds w errors := by
    intro u c hu hc
    have hn := hnoRaw u c (by norm_num [w] at hu ⊢; exact hu) hc
    norm_num [errors] at hn ⊢
    exact hn
  obtain ⟨QA, QB, QC, hQA, hboxA, hQB, hboxB, hQC, hboxC, hflagB, huniversal⟩ :=
    exists_stacked_interpolants_with_recursive_cover (U 0) (U 1)
  have hbranch := selected_recursive_cover U seeds A selected QA QB QC
    huniversal hdegree hcard hvalues
  have hagreement := selected_full_domain_agreement U seeds A selected
    hcard hvalues
  have hfirst := firstResidualCell_count_lt selected seeds QA QB
    hQA hQB hboxA hboxB (U 0) (U 1) hdegree hagreement hnoPencil
  have hsecond := secondResidualCell_count_lt selected seeds QA QB QC
    hQA hQC hboxA hboxB hboxC (U 0) (U 1) hdegree hagreement hnoPencil
  have hfixed : (fixedSeeds selected seeds QA QB QC).card ≤ fixedCost := by
    let Delta := fixedSeeds selected seeds QA QB QC
    let G := gcd123 QA QB QC
    have hGne : G ≠ 0 :=
      ContactStackedBoxTransport6656Research.gcd123_ne_zero (C := QC)
        (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := QB) hQA)
    have hboxG := gcd123_mem_meet_box QA QB QC hQA hQC
      (gcd12_mem_meet_box QA QB hQA (by
        intro hBzero
        subst hBzero
        exact hQA (by simp [gcd12])) hboxA hboxB) hboxC
    have hsupportG := gcd123_support_of_flagB QA QB QC hQA hQB hQC
      hboxA hboxB hboxC hflagB
    have hdegDelta : ∀ gamma ∈ Delta, (selected gamma).natDegree ≤ w :=
      fun gamma hg ↦ hdegree gamma (fixedSeeds_subset selected seeds QA QB QC hg)
    have hagrDelta : ∀ gamma ∈ Delta, agreements ≤
        ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            U 0 i + gamma * U 1 i)).card :=
      fun gamma hg ↦ hagreement gamma (fixedSeeds_subset selected seeds QA QB QC hg)
    have hspecDelta : ∀ gamma ∈ Delta,
        specialization IRSProfile.Field (selected gamma) gamma G = 0 :=
      fun gamma hg ↦ (fixedSeeds_spec selected seeds QA QB QC hg).2.1
    have hnoPencilDelta : NoLargeSelectedPencil selected Delta w errors := by
      intro u c hu hc
      have hsub := fixedSeeds_subset selected seeds QA QB QC
      have hle := hnoPencil u c hu (by
        intro gamma hg
        exact hsub (hc gamma hg))
      exact hle
    exact hfixedProvider G hGne hboxG hsupportG selected Delta (U 0) (U 1)
      hspecDelta hdegDelta hagrDelta hnoPencilDelta
  have hbound := selected_card_le_promotedBudget_of_cell_bounds
    selected seeds QA QB QC hfirst hsecond hfixed
  exact hbound

end

end ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research
