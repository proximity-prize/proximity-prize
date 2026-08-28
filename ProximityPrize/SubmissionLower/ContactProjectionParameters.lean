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
    mixed surfaceVector firstTail unitY = 512491520 ∧
    mixed surfaceVector firstTail unitR = 2317353130 ∧
    mixed surfaceVector firstTail unitZ = 78381062 := by
  norm_num [mixed, surfaceVector, firstTail, tailVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem agreement_cut_projection_values :
    mixed surfaceVector agreementVector unitY = 512487616 ∧
    mixed surfaceVector agreementVector unitR = 2295053406 ∧
    mixed surfaceVector agreementVector unitZ = 77594038 := by
  norm_num [mixed, surfaceVector, agreementVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

def sparseRCap (surfaceY surfaceJoint cutY cutJoint : ℕ) : ℕ :=
  surfaceY * cutJoint + cutY * surfaceJoint - surfaceY * cutY

def firstSparseRCap : ℕ :=
  sparseRCap yCap seedTotalCap firstTail.y (1 + 2 * (w + 1) * seedTotalCap)

def agreementSparseRCap : ℕ :=
  sparseRCap yCap seedTotalCap agreementVector.y (1 + 2 * w * seedTotalCap)

theorem sparse_projection_values :
    firstSparseRCap = 2140143786 ∧ agreementSparseRCap = 2121253234 := by
  norm_num [firstSparseRCap, agreementSparseRCap, sparseRCap, firstTail, tailVector,
    agreementVector, yCap, weightedCap, ContactAlignmentParameters.multiplicity,
    agreements, w, seedTotalCap]

/-- The rectangle gates used by the whole-surface proof and its replacement
sparse base-R gate are all strictly below characteristic.  The legacy
first-cut sparse gate is deliberately absent: no theorem in the current
whole-surface counting path consumes it. -/
theorem projection_caps_below_characteristic :
    mixed surfaceVector firstTail unitY < prime ∧
    mixed surfaceVector firstTail unitZ < prime ∧
    mixed surfaceVector agreementVector unitY < prime ∧
    mixed surfaceVector agreementVector unitZ < prime ∧
    agreementSparseRCap < prime := by
  rcases first_cut_projection_values with ⟨h1, _, h3⟩
  rcases agreement_cut_projection_values with ⟨h4, _, h6⟩
  rw [h1, h3, h4, h6, sparse_projection_values.2]
  norm_num [prime]

end ProximityPrize.SubmissionLower.ContactProjectionParameters

#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.first_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.agreement_cut_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.sparse_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactProjectionParameters.projection_caps_below_characteristic
