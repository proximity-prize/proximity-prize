import ProximityPrize.SubmissionLower.ContactStackedSelectedBound6696Research
import ProximityPrize.SubmissionLower.ContactFixedSelectedCell6696Research

/-!
# Premise-free stacked 66.96 closure

This module supplies the sole fixed-cell premise of the selected-family
composition from the completed sharp-YZ fixed-meet theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedClosure6696Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactInterpolation ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactStackedParameters6696Research
open ContactFixedMeetProfile6696Research
open ContactFixedSelectedCell6696Research
open ContactStackedSelectedBound6696Research
open ContactStackedPromotedArithmetic6696Research
open ContactRobustFixedMeet6656Research

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- The completed fixed-meet theorem discharges the exact abstract fixed-cell
provider used by the recursive-GCD composition. -/
theorem fixedCellCountProvider6696 : FixedCellCountProvider6696 := by
  intro Q hQ hbox selected Delta u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field
      ContactFixedMeetProfile6696Research.prime := by
    simpa [ContactFixedMeetProfile6696Research.prime,
      ContactParameters6600Research.prime] using
        ContactFrozenAlignment6600Research.challenge_field_characteristic6600
  have hbox' : Q ∈ globalCoefficientBox IRSProfile.Field
      fixedProfile.weightedCap fixedProfile.w fixedProfile.seedTotalCap
        fixedProfile.slopeCap := by
    simpa [fixedProfile, agreements, w] using hbox
  have hdegree' : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ fixedProfile.w := by
    simpa [fixedProfile, w] using hdegree
  have hagreement' : ∀ gamma ∈ Delta,
      fixedProfile.agreements ≤
        ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
          (selected gamma).eval (IRSProfile.domain i) =
            u0 i + gamma * u1 i)).card := by
    simpa [fixedProfile, agreements] using hagreement
  have hnoPencil' : NoLargeSelectedPencil selected Delta
      fixedProfile.w fixedProfile.errors := by
    simpa [fixedProfile, Profile.errors, errors, n, agreements, w] using
      hnoPencil
  have h := fixed_selected_count_le_fixedCountCeiling Q hQ hbox'
    selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
    u0 u1 IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree' hsolution hagreement' hnoPencil'
  rw [fixed_count_ceiling_exact] at h
  simpa [fixedCost, fixedRegularCost, fixedSingularCost] using h

theorem selectedNoLargePencilBound6696 :
    SelectedNoLargePencilBound IRSProfile.domain
      131071 79730 274980727623867933 :=
  selectedNoLargePencilBound_of_fixedCellCountProvider6696
    fixedCellCountProvider6696

theorem alignmentBound6696 :
    AffineLineAlignmentBound IRSProfile.baseCode 79730 274980727623867933 := by
  change AffineLineAlignmentBound
    (ReedSolomon.code IRSProfile.domain (131071 + 1))
      79730 274980727623867933
  exact alignmentBound_of_selected_count IRSProfile.domain
    131071 79730 274980727623867933 selectedNoLargePencilBound6696

end

end ProximityPrize.SubmissionLower.ContactStackedClosure6696Research
