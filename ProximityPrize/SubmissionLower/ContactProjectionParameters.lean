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
    mixed surfaceVector firstTail unitY = 312868864 ∧
    mixed surfaceVector firstTail unitR = 2047869145 ∧
    mixed surfaceVector firstTail unitZ = 25952259 := by
  norm_num [mixed, surfaceVector, firstTail, tailVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem agreement_cut_projection_values :
    mixed surfaceVector agreementVector unitY = 312866480 ∧
    mixed surfaceVector agreementVector unitR = 2047853539 ∧
    mixed surfaceVector agreementVector unitZ = 25952061 := by
  norm_num [mixed, surfaceVector, agreementVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem all_projection_caps_below_characteristic :
    mixed surfaceVector firstTail unitY < prime ∧
    mixed surfaceVector firstTail unitR < prime ∧
    mixed surfaceVector firstTail unitZ < prime ∧
    mixed surfaceVector agreementVector unitY < prime ∧
    mixed surfaceVector agreementVector unitR < prime ∧
    mixed surfaceVector agreementVector unitZ < prime := by
  rcases first_cut_projection_values with ⟨h1, h2, h3⟩
  rcases agreement_cut_projection_values with ⟨h4, h5, h6⟩
  rw [h1, h2, h3, h4, h5, h6]
  norm_num [prime]

end ProximityPrize.SubmissionLower.ContactProjectionParameters

#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.first_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.agreement_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.all_projection_caps_below_characteristic
