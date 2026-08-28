import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Exact parameter certificate for the 66.00 residual-incidence candidate

This module records the first integer score-66 cell.  It checks the sparse
interpolation inequality, reconstructs the retained singular contribution
from its geometric formula, and identifies the resulting stratified ledger
with the independently proved residual-incidence arithmetic.

There is no decoding claim in this file: it is the closed arithmetic front
end consumed by the eventual geometric integration.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6600Research

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 100000000000000000

def errors : ℕ := 78842
def agreements : ℕ := n - errors
def multiplicity : ℕ := 26
def seedTotalCap : ℕ := 504
def slopeCap : ℕ := 7
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

/-- Number of monomials in the strict weighted interpolation box.  All
subtractions are natural-number positive parts, exactly as in the production
interpolation construction. -/
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

def unitZ : DegreeVector := ⟨0, 0, 1⟩
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

/-- Singular-branch numerator over one factor of `gap`, retained unchanged
by the nested residual-incidence improvement to the regular branch. -/
def retainedSingularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      mixed liftedSurface implicitCut liftedLast +
      (errors + 1) * mixed liftedSurface implicitCut unitZ) +
    (n - w) * mixed liftedSurface implicitCut liftedAgreement

/-- The singular contribution uses the common `gap^2` denominator. -/
def retainedSingularContribution : ℕ := gap * retainedSingularNumerator

theorem parameter_values :
    agreements = 183302 ∧ weightedCap = 4765852 ∧ yCap = 36 ∧
    gap = 52231 ∧ algebraicCap = 6552 ∧
    implicitWeightedCap = 61956076 ∧ implicitYCap = 472 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 289762688264 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 1105344 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 289759297536 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 3390728 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem characteristic_gates :
    weightedCap < prime ∧ implicitWeightedCap < prime ∧
      algebraicCap < prime ∧ slopeCap < prime := by
  norm_num [weightedCap, multiplicity, agreements, n, errors,
    implicitWeightedCap, algebraicCap, slopeCap, seedTotalCap, prime]

theorem retained_singular_numerator_exact :
    retainedSingularNumerator = 60364133681350647096 := by
  norm_num [retainedSingularNumerator, liftedSurface, implicitCut,
    liftedLast, liftedAgreement, unitZ, mixed, implicitYCap,
    implicitWeightedCap, algebraicCap, yCap, weightedCap, multiplicity,
    agreements, n, errors, w, gap, slopeCap, seedTotalCap]

theorem retained_singular_contribution_exact :
    retainedSingularContribution = 3152879066310625648471176 := by
  rw [show retainedSingularContribution =
      gap * retainedSingularNumerator by rfl,
    retained_singular_numerator_exact]
  norm_num [gap, agreements, n, errors, w]

theorem retained_singular_matches_residual_ledger :
    retainedSingularContribution =
      ContactNearPencil6600ArithmeticResearch.retainedSingularContribution := by
  rw [retained_singular_contribution_exact]
  rfl

theorem exact_stratified_ledger :
    ContactNearPencil6600ArithmeticResearch.stratifiedTotalNumerator =
        246765134551456838376053721 ∧
      ContactNearPencil6600ArithmeticResearch.ledgerCeiling =
        90453862518401229 ∧
      ContactNearPencil6600ArithmeticResearch.alignmentBudget -
          ContactNearPencil6600ArithmeticResearch.ledgerCeiling =
        9546137481598771 := by
  exact ⟨ContactNearPencil6600ArithmeticResearch.stratified_total_exact,
    ContactNearPencil6600ArithmeticResearch.ledger_ceiling_exact,
    ContactNearPencil6600ArithmeticResearch.budget_slack⟩

theorem strict_alignment_budget :
    ContactNearPencil6600ArithmeticResearch.stratifiedTotalNumerator <
      alignmentBudget * gap ^ 2 := by
  rw [ContactNearPencil6600ArithmeticResearch.stratified_total_exact]
  norm_num [alignmentBudget, gap, agreements, n, errors, w]

end ProximityPrize.SubmissionLower.ContactParameters6600Research

#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.retained_singular_contribution_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.strict_alignment_budget
