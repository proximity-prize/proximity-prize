import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Exact parameter certificate for the 66.69 residual-incidence candidate

This module records the integer score-66.69 cell. It checks the sparse
interpolation inequality, reconstructs the retained singular contribution
from its geometric formula, and identifies the resulting stratified ledger
with the independently proved residual-incidence arithmetic.
-/

namespace ProximityPrize.SubmissionLower.ContactParameters6600Research

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 137490364055697543

def errors : ℕ := 79461
def agreements : ℕ := n - errors
def multiplicity : ℕ := 31
def seedTotalCap : ℕ := 1495
def slopeCap : ℕ := 8
def weightedCap : ℕ := multiplicity * agreements
def yCap : ℕ := (weightedCap - 1) / w
def gap : ℕ := agreements - w
def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

def coefficientCount : ℕ :=
  ∑ i ∈ range (seedTotalCap + 1),
    ∑ j ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - i) *
        (weightedCap - w * i - (w - 1) * j)

def contactExponent (r : ℕ) : ℕ := min (r + 1) (multiplicity - r)

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

def retainedSingularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      mixed liftedSurface implicitCut liftedLast +
      (errors + 1) * mixed liftedSurface implicitCut unitZ) +
    (n - w) * mixed liftedSurface implicitCut liftedAgreement

def retainedSingularContribution : ℕ := gap * retainedSingularNumerator

theorem parameter_values :
    agreements = 182683 ∧ weightedCap = 5663173 ∧ yCap = 43 ∧
    gap = 51612 ∧ algebraicCap = 22425 ∧
    implicitWeightedCap = 84947595 ∧ implicitYCap = 648 := by
  norm_num [agreements, n, errors, weightedCap, multiplicity, yCap, w,
    gap, algebraicCap, slopeCap, seedTotalCap, implicitWeightedCap,
    implicitYCap]

theorem coefficient_count_exact : coefficientCount = 1384988026260 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    multiplicity, agreements, n, errors, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 5283288 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 1384982249472 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 5776788 := by
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
    retainedSingularNumerator = 383759373639176231841 := by
  norm_num [retainedSingularNumerator, liftedSurface, implicitCut,
    liftedLast, liftedAgreement, unitZ, mixed, implicitYCap,
    implicitWeightedCap, algebraicCap, yCap, weightedCap, multiplicity,
    agreements, n, errors, w, gap, slopeCap, seedTotalCap]

theorem retained_singular_contribution_exact :
    retainedSingularContribution = 19806588792265163677777692 := by
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
        171109661551263794831504892 ∧
      ContactNearPencil6600ArithmeticResearch.ledgerCeiling =
        64235211005980562 ∧
      ContactNearPencil6600ArithmeticResearch.alignmentBudget -
          ContactNearPencil6600ArithmeticResearch.ledgerCeiling =
        73255153049716981 := by
  exact ⟨ContactNearPencil6600ArithmeticResearch.stratified_total_exact,
    ContactNearPencil6600ArithmeticResearch.ledger_ceiling_exact,
    ContactNearPencil6600ArithmeticResearch.budget_slack⟩

theorem strict_alignment_budget :
    ContactNearPencil6600ArithmeticResearch.stratifiedTotalNumerator <
      alignmentBudget * gap ^ 2 := by
  rw [ContactNearPencil6600ArithmeticResearch.stratified_total_exact]
  norm_num [alignmentBudget, gap, agreements, n, errors, w]

end ProximityPrize.SubmissionLower.ContactParameters6600Research
