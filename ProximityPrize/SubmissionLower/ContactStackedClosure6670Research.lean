import ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research
import ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research

/-!
# Premise-free stacked 66.70 closure

This module supplies the sole fixed-cell premise of the selected-family
composition from the completed sharp-YZ fixed-meet theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedClosure6670Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactInterpolation ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactStackedParameters6670Research
open ContactFixedMeetProfile6670Research
open ContactFixedSelectedCell6670Research
open ContactStackedSelectedBound6670Research
open ContactStackedPromotedArithmetic6670Research
open ContactRobustFixedMeet6656Research

noncomputable section

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- The completed fixed-meet theorem discharges the exact abstract fixed-cell
provider used by the recursive-GCD composition. -/
theorem fixedCellCountProvider6670 : FixedCellCountProvider6670 := by
  intro Q hQ hbox selected Delta u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field
      ContactFixedMeetProfile6670Research.prime := by
    simpa [ContactFixedMeetProfile6670Research.prime,
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

theorem selectedNoLargePencilBound6670 :
    SelectedNoLargePencilBound IRSProfile.domain
      131071 79476 137490364055697543 :=
  selectedNoLargePencilBound_of_fixedCellCountProvider6670
    fixedCellCountProvider6670

theorem protocolClaim6670 : ProtocolClaim 6670 317907 1048576 :=
  protocolClaim6670_of_fixedCellCountProvider6670 fixedCellCountProvider6670

end

end ProximityPrize.SubmissionLower.ContactStackedClosure6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedClosure6670Research.fixedCellCountProvider6670
#print axioms ProximityPrize.SubmissionLower.ContactStackedClosure6670Research.selectedNoLargePencilBound6670
#print axioms ProximityPrize.SubmissionLower.ContactStackedClosure6670Research.protocolClaim6670
