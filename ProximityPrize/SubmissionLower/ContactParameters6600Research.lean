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
def alignmentBudget : ℕ := 137490364055697543

def errors : ℕ := 78995
def agreements : ℕ := n - errors
def multiplicity : ℕ := 31
def seedTotalCap : ℕ := 520
def slopeCap : ℕ := 8
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
    agreements = 183149 ∧ weightedCap = 5677619 ∧ yCap = 43 ∧
    gap = 52078 ∧ algebraicCap = 7800 ∧
    implicitWeightedCap = 85164285 ∧ implicitYCap = 649 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 477125921970 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 1820088 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 477125148672 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 773298 := by
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
    retainedSingularNumerator = 135232596916990567689 := by
  norm_num [retainedSingularNumerator, liftedSurface, implicitCut,
    liftedLast, liftedAgreement, unitZ, mixed, implicitYCap,
    implicitWeightedCap, algebraicCap, yCap, weightedCap, multiplicity,
    agreements, n, errors, w, gap, slopeCap, seedTotalCap]

theorem retained_singular_contribution_exact :
    retainedSingularContribution = 7042643182243034784107742 := by
  rw [show retainedSingularContribution =
      gap * retainedSingularNumerator by rfl,
    retained_singular_numerator_exact]
  norm_num [gap, agreements, n, errors, w]

theorem retained_singular_matches_residual_ledger :
    retainedSingularContribution =
      ContactNearPencil6600ArithmeticResearch.retainedSingularContribution := by
  rw [retained_singular_contribution_exact]
  rfl


end ProximityPrize.SubmissionLower.ContactParameters6600Research

#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.coefficient_count_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.local_contact_rank_exact
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactParameters6600Research.retained_singular_contribution_exact
