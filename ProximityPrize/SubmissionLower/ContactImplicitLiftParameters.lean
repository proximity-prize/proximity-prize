import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentParameters

/-!
# Exact arithmetic for the implicit-equation contact lift

Model label: gpt-5.

This verifies the coarser numerical ledger obtained by lifting an implicit
equation J to J_X+R*J_Y and reusing the contact-curve counting machinery.
The reduction and geometric bounds are separate formal obligations.
No complete alignment theorem or competition submission is asserted.
-/

namespace ProximityPrize.SubmissionLower.ContactImplicitLiftParameters

open ContactAlignmentParameters

def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w
def liftedSurface : DegreeVector := ⟨implicitYCap, 1, algebraicCap⟩
def implicitCut : DegreeVector := ⟨implicitYCap, 0, algebraicCap⟩
def liftedLastTail : DegreeVector :=
  ⟨1 + 2 * implicitWeightedCap * implicitYCap,
    implicitWeightedCap, 2 * implicitWeightedCap * algebraicCap⟩
def liftedAgreement : DegreeVector :=
  ⟨1 + 2 * w * implicitYCap, w, 2 * w * algebraicCap + 1⟩

def liftedSingularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
    mixed liftedSurface implicitCut liftedLastTail +
    (errors + 1) * mixed liftedSurface implicitCut unitZ) +
  (n - w) * mixed liftedSurface implicitCut liftedAgreement

def liftedTotalNumerator : ℕ := regularNumerator + gap * liftedSingularNumerator

theorem lifted_parameter_values :
    implicitWeightedCap = 38553185 ∧ implicitYCap = 294 ∧
    liftedLastTail = ⟨22669272781, 38553185, 144188911900⟩ ∧
    liftedAgreement = ⟨77069749, 131071, 490205541⟩ := by
  norm_num [implicitWeightedCap, implicitYCap, liftedLastTail, liftedAgreement,
    algebraicCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements,
    w, slopeCap, seedTotalCap]

theorem lifted_projection_values :
    mixed liftedSurface implicitCut unitY = 1870 ∧
    mixed liftedSurface implicitCut unitR = 1099560 ∧
    mixed liftedSurface implicitCut unitZ = 294 := by
  norm_num [mixed, liftedSurface, implicitCut, implicitYCap, implicitWeightedCap,
    unitY, unitR, unitZ, algebraicCap, weightedCap,
    ContactAlignmentParameters.multiplicity, agreements, w, slopeCap, seedTotalCap]

theorem lifted_projection_characteristic_gates :
    implicitWeightedCap < prime ∧
    mixed liftedSurface implicitCut unitY < prime ∧
    mixed liftedSurface implicitCut unitR < prime ∧
    mixed liftedSurface implicitCut unitZ < prime := by
  rcases lifted_projection_values with ⟨hY, hR, hZ⟩
  rw [hY, hR, hZ, lifted_parameter_values.1]
  norm_num [prime]

theorem lifted_singular_numerator_exact :
    liftedSingularNumerator = 6847034160268716852 := by
  norm_num [liftedSingularNumerator, mixed, liftedSurface, implicitCut, liftedLastTail,
    liftedAgreement, implicitYCap, implicitWeightedCap, unitZ, algebraicCap,
    weightedCap, ContactAlignmentParameters.multiplicity, agreements, w, gap,
    errors, n, slopeCap, seedTotalCap]

theorem lifted_total_numerator_exact :
    liftedTotalNumerator = 175519046503579286162901852 := by
  rw [liftedTotalNumerator, lifted_singular_numerator_exact]
  norm_num [regularNumerator, cutNumerator, wholeNumerator, mixed,
    firstTail, lastTail, tailVector, agreementVector, unitY, unitR, unitZ,
    yCap, weightedCap, ContactAlignmentParameters.multiplicity, agreements,
    w, gap, errors, n, slopeCap, seedTotalCap]

theorem lifted_division_certificate :
    liftedTotalNumerator = 61565772992518152 * gap ^ 2 + 2546929980 ∧
    2546929980 < gap ^ 2 := by
  rw [lifted_total_numerator_exact, denominator_exact]
  norm_num

theorem lifted_strict_budget :
    liftedTotalNumerator < alignmentBudget * gap ^ 2 := by
  rw [lifted_total_numerator_exact, denominator_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactImplicitLiftParameters

#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_parameter_values
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_projection_values
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_projection_characteristic_gates
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_singular_numerator_exact
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_total_numerator_exact
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_division_certificate
#print axioms ProximityPrize.SubmissionLower.ContactImplicitLiftParameters.lifted_strict_budget
