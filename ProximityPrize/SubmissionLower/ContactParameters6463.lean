import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic for the standard triangular 64.63-bit contact row

This is the `e = 77416`, `m = 18`, `L = 175`, `s = 5` row.  It combines
the existing triangular interpolation space with the sharp incidence ledger
and the joint `(Y,Z)` Newton/Sylvester projection cap.  This module contains
only closed arithmetic certificates; the geometric sharp-incidence and
joint-support adapters remain separate obligations.

No native-decision axiom is used.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6463

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 100000000000000000

def errors : ℕ := 77416
def agreements : ℕ := n - errors
def multiplicity : ℕ := 18
def seedTotalCap : ℕ := 175
def slopeCap : ℕ := 5
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap

/-- Exact dimension of the standard triangular coefficient space. -/
def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

/-- Exact rank of one translated order-`multiplicity` contact block. -/
def localContactRank : ℕ :=
  ∑ r ∈ range multiplicity,
    (((slopeCap + 1) *
        (∑ f ∈ range (min r seedTotalCap + 1),
          (seedTotalCap + 1 - f))) -
      ((slopeCap + 1 - contactExponent r) *
        (∑ f ∈ range (min r seedTotalCap + 1 - contactExponent r),
          (seedTotalCap + 1 - contactExponent r - f))))

def totalContactRank : ℕ := n * localContactRank
def rankMargin : ℕ := coefficientCount - totalContactRank

structure DegreeVector where
  y : ℕ
  r : ℕ
  z : ℕ
  deriving DecidableEq

def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitY : DegreeVector := ⟨1, 0, 0⟩
def unitR : DegreeVector := ⟨0, 1, 0⟩
def unitZ : DegreeVector := ⟨0, 0, 1⟩

def surfaceVector : DegreeVector := ⟨yCap, slopeCap, seedTotalCap⟩

def tailVector (h : ℕ) : DegreeVector :=
  ⟨1 + 2 * h * yCap,
    h * (2 * slopeCap - 1),
    2 * h * seedTotalCap⟩

def firstTail : DegreeVector := tailVector (w + 1)
def agreementVector : DegreeVector :=
  ⟨1 + 2 * w * yCap,
    w * (2 * slopeCap - 1),
    2 * w * seedTotalCap + 1⟩

def firstTailSeedTotal : ℕ := 1 + 2 * (w + 1) * seedTotalCap
def agreementSeedTotal : ℕ := 1 + 2 * w * seedTotalCap

/-- The trapezoidal Sylvester bound for the first-tail projection. -/
def refinedFirstProjection : ℕ :=
  firstTail.y * seedTotalCap + yCap * firstTailSeedTotal - yCap * firstTail.y

/-- The trapezoidal Sylvester bound for the agreement projection. -/
def refinedAgreementProjection : ℕ :=
  agreementVector.y * seedTotalCap + yCap * agreementSeedTotal -
    yCap * agreementVector.y

def refinedProjectionMax : ℕ := max refinedFirstProjection refinedAgreementProjection

def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w
def implicitProjectionMax : ℕ := 2 * implicitYCap * algebraicCap

def liftedSurface : DegreeVector := ⟨implicitYCap, 1, algebraicCap⟩
def implicitCut : DegreeVector := ⟨implicitYCap, 0, algebraicCap⟩
def liftedLast : DegreeVector :=
  ⟨1 + 2 * implicitWeightedCap * implicitYCap,
    implicitWeightedCap,
    2 * implicitWeightedCap * algebraicCap⟩
def liftedAgreement : DegreeVector :=
  ⟨1 + 2 * w * implicitYCap,
    w,
    2 * w * algebraicCap + 1⟩

/-- Sharp whole-surface numerator over the denominator `gap^2`. -/
def sharpWholeNumerator : ℕ :=
  (n - w) ^ 2 * mixed surfaceVector agreementVector agreementVector +
  (errors + 1) * (n - w) * gap *
    mixed surfaceVector agreementVector unitZ

/-- Sharp singular-branch numerator over the denominator `gap`. -/
def sharpSingularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      mixed liftedSurface implicitCut liftedLast +
      (errors + 1) * mixed liftedSurface implicitCut unitZ) +
    (n - w) * mixed liftedSurface implicitCut liftedAgreement

def sharpTotalNumerator : ℕ :=
  sharpWholeNumerator + gap * sharpSingularNumerator

def gapSquared : ℕ := gap ^ 2
def sharpLedgerCeiling : ℕ :=
  (sharpTotalNumerator + gapSquared - 1) / gapSquared

theorem parameter_values :
    agreements = 184728 ∧ weightedCap = 3325104 ∧ yCap = 25 ∧
    gap = 53657 ∧ algebraicCap = 1575 ∧
    implicitWeightedCap = 29925936 ∧ implicitYCap = 228 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 36400718089 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 138857 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 36400529408 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 188681 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem rectangular_projection_values :
    mixed surfaceVector firstTail unitY = 435814400 ∧
    mixed surfaceVector agreementVector unitY = 435811080 ∧
    mixed surfaceVector firstTail unitR = 2293760175 ∧
    mixed surfaceVector agreementVector unitR = 2293742700 ∧
    mixed surfaceVector firstTail unitZ = 62259205 ∧
    mixed surfaceVector agreementVector unitZ = 62258730 := by
  norm_num [surfaceVector, firstTail, tailVector, agreementVector, unitY,
    unitR, unitZ, mixed, yCap, weightedCap, multiplicity, agreements, n,
    errors, w, seedTotalCap, slopeCap]

theorem refined_projection_values :
    refinedFirstProjection = 2129920175 ∧
    refinedAgreementProjection = 2129903925 ∧
    refinedProjectionMax = 2129920175 := by
  norm_num [refinedFirstProjection, refinedAgreementProjection,
    refinedProjectionMax, firstTail, tailVector, agreementVector,
    firstTailSeedTotal, agreementSeedTotal, yCap, weightedCap, multiplicity,
    agreements, n, errors, w, seedTotalCap, slopeCap]

theorem old_projection_gate_fails :
    prime ≤ mixed surfaceVector firstTail unitR := by
  rw [rectangular_projection_values.2.2.1]
  norm_num [prime]

theorem refined_projection_gate : refinedProjectionMax < prime := by
  rw [refined_projection_values.2.2]
  norm_num [prime]

theorem refined_projection_slack :
    prime - refinedProjectionMax = 786258 := by
  rw [refined_projection_values.2.2]
  norm_num [prime]

theorem implicit_parameter_values :
    implicitProjectionMax = 718200 ∧
    implicitWeightedCap = 29925936 ∧ implicitYCap = 228 := by
  norm_num [implicitProjectionMax, implicitWeightedCap, implicitYCap,
    algebraicCap, slopeCap, seedTotalCap, weightedCap, multiplicity,
    agreements, n, errors, w]

theorem characteristic_gates :
    refinedProjectionMax < prime ∧ implicitProjectionMax < prime ∧
    implicitWeightedCap < prime ∧ algebraicCap < prime ∧ slopeCap < prime := by
  exact ⟨refined_projection_gate, by
    rw [implicit_parameter_values.1, implicit_parameter_values.2.1]
    norm_num [prime, algebraicCap, slopeCap, seedTotalCap]⟩

theorem sharp_whole_exact :
    sharpWholeNumerator = 144656388802427997131975700 := by
  norm_num [sharpWholeNumerator, surfaceVector, agreementVector, unitZ, mixed,
    yCap, weightedCap, multiplicity, slopeCap, seedTotalCap, w, n, errors,
    gap, agreements]

theorem sharp_singular_exact :
    sharpSingularNumerator = 3496735633313991351 := by
  norm_num [sharpSingularNumerator, liftedSurface, implicitCut, liftedLast,
    liftedAgreement, unitZ, mixed, implicitYCap, implicitWeightedCap,
    algebraicCap, yCap, weightedCap, multiplicity, agreements, n, errors, w,
    gap, slopeCap, seedTotalCap]

theorem sharp_total_exact :
    sharpTotalNumerator = 144844013146304725965896307 := by
  rw [show sharpTotalNumerator =
      sharpWholeNumerator + gap * sharpSingularNumerator by rfl,
    sharp_whole_exact, sharp_singular_exact]
  norm_num [gap, agreements, n, errors, w]

theorem gap_squared_exact : gapSquared = 2879073649 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

theorem sharp_division_certificate :
    sharpTotalNumerator =
        50309242070488182 * gapSquared + 603780189 ∧
      603780189 < gapSquared := by
  rw [sharp_total_exact, gap_squared_exact]
  norm_num

theorem sharp_ledger_ceiling_exact :
    sharpLedgerCeiling = 50309242070488183 := by
  norm_num [sharpLedgerCeiling, sharp_total_exact, gap_squared_exact]

theorem sharp_ledger_budget_slack :
    alignmentBudget - sharpLedgerCeiling = 49690757929511817 := by
  rw [sharp_ledger_ceiling_exact]
  norm_num [alignmentBudget]

theorem sharp_strict_budget :
    sharpTotalNumerator < alignmentBudget * gapSquared := by
  rw [sharp_total_exact, gap_squared_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactParameters6463

#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.refined_projection_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.sharp_total_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.sharp_division_certificate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6463.sharp_strict_budget
