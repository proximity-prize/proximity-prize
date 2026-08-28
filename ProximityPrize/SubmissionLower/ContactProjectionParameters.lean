import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentParameters

/-!
# Characteristic-safe coordinate-projection budgets

Model label: gpt-5.

These are exact inequalities for the frozen contact witness, not a proof of
the geometric degree bounds. Once actual projection degrees are bounded by
the corresponding mixed expressions, every one is below characteristic.
This does not assert separability of arbitrary test functions.
-/

namespace ProximityPrize.SubmissionLower.ContactProjectionParameters

open ContactAlignmentParameters

def surfaceVector : DegreeVector := ⟨yCap, slopeCap, seedTotalCap⟩

theorem first_cut_projection_values :
    mixed surfaceVector firstTail unitY = 438304768 ∧
    mixed surfaceVector firstTail unitR = 2306867376 ∧
    mixed surfaceVector firstTail unitZ = 62259205 := by
  norm_num [mixed, surfaceVector, firstTail, tailVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem agreement_cut_projection_values :
    mixed surfaceVector agreementVector unitY = 438301429 ∧
    mixed surfaceVector agreementVector unitR = 2283781305 ∧
    mixed surfaceVector agreementVector unitZ = 61603375 := by
  norm_num [mixed, surfaceVector, agreementVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem outer_agreement_projection_caps_below_characteristic :
    mixed surfaceVector agreementVector unitY < prime ∧
    mixed surfaceVector agreementVector unitZ < prime := by
  rcases agreement_cut_projection_values with ⟨hY, _, hZ⟩
  rw [hY, hZ]
  norm_num [prime]

end ProximityPrize.SubmissionLower.ContactProjectionParameters

#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.first_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.agreement_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.outer_agreement_projection_caps_below_characteristic
