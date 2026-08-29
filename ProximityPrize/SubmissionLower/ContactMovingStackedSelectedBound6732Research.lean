import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactMovingStackedInterpolation6732Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
import ProximityPrize.SubmissionLower.ContactMovingStackedBoxTransport6732Research
import ProximityPrize.SubmissionLower.ContactMovingStackedResidualCells6732Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6732Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactMovingParameters6732Research
open ContactMovingStackedInterpolation6732Research
open ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactMovingStackedBoxTransport6732Research
open ContactMovingStackedResidualCells6732Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

def FixedCellCountProvider6732 : Prop :=
  ∀ (Q : GlobalPoly)
    (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox IRSProfile.Field
      (profileFinalMeet.multiplicity * agreements) w
      profileFinalMeet.seedCap profileFinalMeet.slopeCap)
    (Hsupport : ResidualSupportData
      ContactMovingStackedBoxTransport6732Research.fixedSupport Q)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (Delta : Finset IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hsolution : ∀ gamma ∈ Delta,
      specialization IRSProfile.Field (selected gamma) gamma Q = 0)
    (hdegree : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Delta,
      agreements ≤
        (Finset.univ.filter (fun i => (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Delta w errors),
    Delta.card ≤ fixedCost

theorem selectedNoLargePencilBound6732_of_fixedProvider
    (hfixed : FixedCellCountProvider6732) :
    SelectedNoLargePencilBound
      IRSProfile.domain 131071 80092 274980727111395087 := by
  intro u0 u1
  rcases exists_stacked_interpolants_with_recursive_cover u0 u1 with
    ⟨QA, QB, QC, hQA_ne, hboxA, hQB_ne, hboxB, hQC_ne, hboxC, hflagB, huniv⟩
  let hgcd := gcd123_support_of_flagB QA QB QC hQA_ne hQB_ne hQC_ne hboxA hboxB hboxC hflagB
  have hfixed_bound : ∀ gamma : IRSProfile.Field,
      (fixedCell IRSProfile.Field gamma QA QB QC).card ≤ fixedCost := by
    intro gamma
    have hsub :
        (fixedCell IRSProfile.Field gamma QA QB QC) ⊆
          selectedSeedSet IRSProfile.Field gamma QA QB QC := by
      exact fixedCell_subset_selectedSeedSet IRSProfile.Field gamma QA QB QC
    have hnoPencil : NoLargeSelectedPencil (fun _ => 0) ∅ w errors := by
      intro P hP hcard; simp at hcard
    have hcard := hfixed (gcd123 QA QB QC)
      (ContactStackedBoxTransport6656Research.gcd123_ne_zero
        (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := QB) hQA_ne) QC hQC_ne)
      (gcd123_mem_meet_box QA QB QC hQA_ne hQC_ne
        (gcd12_mem_meet_box QA QB hQA_ne hQB_ne hboxA hboxB) hboxC)
      hgcd (fun _ => 0) ∅ u0 u1
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      (by intro g hg; simp at hg)
      hnoPencil
    exact fixedCell_count_le QA QB QC gamma hQA_ne hQB_ne hQC_ne
      hboxA hboxB hboxC hflagB hfixed
  have hres1_bound : ∀ gamma : IRSProfile.Field,
      (firstResidualCell IRSProfile.Field gamma QA QB).card <
        firstResidualCeiling := by
    intro gamma
    exact firstResidualCell_count_lt QA QB QC gamma hQA_ne hQB_ne hboxA hboxB
  have hres2_bound : ∀ gamma : IRSProfile.Field,
      (secondResidualCell IRSProfile.Field gamma QA QB QC).card <
        secondResidualCeiling := by
    intro gamma
    exact secondResidualCell_count_lt QA QB QC gamma hQA_ne hQB_ne hQC_ne hboxA hboxB hboxC
  have htotal : ∀ gamma : IRSProfile.Field,
      (selectedSeedSet IRSProfile.Field gamma QA QB QC).card < mcaBudget := by
    intro gamma
    have hpart := selectedSeedSet_card_eq_sum IRSProfile.Field gamma QA QB QC
    have hsum :
        (fixedCell IRSProfile.Field gamma QA QB QC).card +
            (firstResidualCell IRSProfile.Field gamma QA QB).card +
            (secondResidualCell IRSProfile.Field gamma QA QB QC).card <
          fixedCost + firstResidualCeiling + secondResidualCeiling := by
      have hf := hfixed_bound gamma
      have hr1 := hres1_bound gamma
      have hr2 := hres2_bound gamma
      omega
    have htot := total_and_slack_exact.2.2
    omega
  refine ⟨QA, QB, QC, ?_⟩
  intro gamma P support hP hcard hvalues
  have hbranch := huniv gamma P support hP hcard hvalues
  have hcard_bound := htotal gamma
  omega

end

end ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6732Research
