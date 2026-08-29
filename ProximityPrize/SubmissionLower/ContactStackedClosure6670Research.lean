import ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research
import ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research
import ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch

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
  intro Q hQ hbox Hsupport selected Delta u0 u1 hsolution hdegree hagreement hnoPencil
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
  have h := fixed_selected_count_le_fixedCountCeiling Q hQ hbox' Hsupport
    selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
    u0 u1 IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree' hsolution hagreement' hnoPencil'
  rw [fixed_count_ceiling_exact] at h
  simpa [fixedCost, fixedRegularCost, fixedSingularCost] using h

theorem selectedNoLargePencilBound6670 :
    SelectedNoLargePencilBound IRSProfile.domain
      131071 79866 274980727511395087 :=
  selectedNoLargePencilBound_of_fixedCellCountProvider6670
    fixedCellCountProvider6670

/-- Final split-budget endpoint: the recursive-GCD construction supplies
MCA, while the independent fixed-centre construction supplies Lambda. -/
theorem protocolClaim6710 : ProtocolClaim 6710 319467 1048576 := by
  have halign : AffineLineAlignmentBound IRSProfile.baseCode
      ContactSeedlessProtocolResearch.errors
      ContactSeedlessProtocolResearch.mcaBudget := by
    have h := ContactAlignmentBridge.alignmentBound_of_selected_count
      IRSProfile.domain 131071 79866 274980727511395087
      selectedNoLargePencilBound6670
    simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
      ContactSeedlessProtocolResearch.errors,
      ContactSeedlessProtocolResearch.mcaBudget,
      ContactScore6630Research.errors6630] using h
  exact ContactSeedlessProtocolResearch.protocolClaim6710_of_alignment halign

end

end ProximityPrize.SubmissionLower.ContactStackedClosure6670Research
