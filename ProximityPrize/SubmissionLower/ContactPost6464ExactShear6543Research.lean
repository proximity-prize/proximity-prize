import ProximityPrize.Benchmark.TargetLower

/-!
# Conditional exact arithmetic for the post-6464 Newton/shear row

Research-only module for `(e,m,s,L) = (78210,19,5,371)`.  The interpolation
rank and every ledger operation are proved here.  The two declared mixed
caps are the output required from the separate sparse-eliminant geometry:

* `16230040480658160` for `MV(Sh(P),Sh(E),Sh(E))`;
* `58195529` for `MV(Sh(P),Sh(E),[0,eZ])`.

This file deliberately does **not** claim those two geometric facts.  It
shows exactly what they buy once supplied: score cell `78210` fits below
the `10^17` ledger ceiling, while retaining a positive interpolation margin.
-/

namespace ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research

open Finset
open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def alignmentBudget : ℕ := 100000000000000000

def errors : ℕ := 78210
def agreements : ℕ := n - errors
def multiplicity : ℕ := 19
def seedTotalCap : ℕ := 371
def slopeCap : ℕ := 5
def weightedCap : ℕ := multiplicity * agreements
def gap : ℕ := agreements - w

def coefficientCount : ℕ :=
  ∑ y ∈ range (seedTotalCap + 1),
    ∑ r ∈ range (slopeCap + 1),
      (seedTotalCap + 1 - y) *
        (weightedCap - w * y - (w - 1) * r)

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

def mixed (a b c : DegreeVector) : ℕ :=
  a.y * b.r * c.z + a.y * b.z * c.r +
  a.r * b.y * c.z + a.r * b.z * c.y +
  a.z * b.y * c.r + a.z * b.r * c.y

def unitZ : DegreeVector := ⟨0, 0, 1⟩

/-- Geometric input expected from the exact sheared Newton eliminant. -/
def shearedWholeMixedCap : ℕ := 16230040480658160

/-- This cap is invariant under the `R ↦ R+Z` shear. -/
def shearedZMixedCap : ℕ := 58195529

def algebraicCap : ℕ := (2 * slopeCap - 1) * seedTotalCap
def implicitWeightedCap : ℕ := (2 * slopeCap - 1) * weightedCap
def implicitYCap : ℕ := (implicitWeightedCap - 1) / w

def liftedSurface : DegreeVector := ⟨implicitYCap, 1, algebraicCap⟩
def implicitCut : DegreeVector := ⟨implicitYCap, 0, algebraicCap⟩
def liftedLast : DegreeVector :=
  ⟨1 + 2 * implicitWeightedCap * implicitYCap,
    implicitWeightedCap,
    2 * implicitWeightedCap * algebraicCap⟩
def liftedAgreement : DegreeVector :=
  ⟨1 + 2 * w * implicitYCap, w, 2 * w * algebraicCap + 1⟩

def wholeNumerator : ℕ :=
  (n - w) ^ 2 * shearedWholeMixedCap +
    (errors + 1) * (n - w) * gap * shearedZMixedCap

def singularNumerator : ℕ :=
  gap * (algebraicCap + 2 * algebraicCap ^ 2 +
      mixed liftedSurface implicitCut liftedLast +
      (errors + 1) * mixed liftedSurface implicitCut unitZ) +
    (n - w) * mixed liftedSurface implicitCut liftedAgreement

def totalNumerator : ℕ := wholeNumerator + gap * singularNumerator
def gapSquared : ℕ := gap ^ 2
def ledgerCeiling : ℕ :=
  (totalNumerator + gapSquared - 1) / gapSquared

theorem parameter_values :
    agreements = 183934 ∧ weightedCap = 3494746 ∧ gap = 52863 ∧
      algebraicCap = 3339 ∧ implicitWeightedCap = 31452714 ∧
      implicitYCap = 239 := by
  norm_num [agreements, weightedCap, gap, algebraicCap, implicitWeightedCap,
    implicitYCap, n, w, errors, multiplicity, slopeCap, seedTotalCap]

theorem coefficient_count_exact : coefficientCount = 87521016352 := by
  norm_num [coefficientCount, seedTotalCap, slopeCap, weightedCap,
    agreements, n, errors, multiplicity, w, Finset.sum_range_succ]

theorem local_contact_rank_exact : localContactRank = 333865 := by
  norm_num [localContactRank, contactExponent, multiplicity, seedTotalCap,
    slopeCap, Finset.sum_range_succ]

theorem total_contact_rank_exact : totalContactRank = 87520706560 := by
  rw [show totalContactRank = n * localContactRank by rfl,
    local_contact_rank_exact]
  norm_num [n]

theorem rank_margin_exact : rankMargin = 309792 := by
  rw [show rankMargin = coefficientCount - totalContactRank by rfl,
    coefficient_count_exact, total_contact_rank_exact]

theorem interpolation_gate : totalContactRank < coefficientCount := by
  rw [coefficient_count_exact, total_contact_rank_exact]
  norm_num

theorem whole_numerator_exact :
    wholeNumerator = 278865764087117747037504021 := by
  norm_num [wholeNumerator, shearedWholeMixedCap, shearedZMixedCap,
    n, w, errors, gap, agreements]

theorem singular_numerator_exact :
    singularNumerator = 8043405963321174171 := by
  norm_num [singularNumerator, liftedSurface, implicitCut, liftedLast,
    liftedAgreement, unitZ, mixed, implicitYCap, implicitWeightedCap,
    algebraicCap, weightedCap, slopeCap, seedTotalCap, multiplicity,
    agreements, n, errors, w, gap]

theorem total_numerator_exact :
    totalNumerator = 279290962656556794267705594 := by
  rw [show totalNumerator = wholeNumerator + gap * singularNumerator by rfl,
    whole_numerator_exact, singular_numerator_exact]
  norm_num [gap, agreements, n, errors, w]

theorem gap_squared_exact : gapSquared = 2794496769 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

theorem ledger_ceiling_exact : ledgerCeiling = 99943204713920639 := by
  norm_num [ledgerCeiling, total_numerator_exact, gap_squared_exact]

theorem ledger_budget_slack :
    alignmentBudget - ledgerCeiling = 56795286079361 := by
  rw [ledger_ceiling_exact]
  norm_num [alignmentBudget]

theorem strict_budget : totalNumerator < alignmentBudget * gapSquared := by
  rw [total_numerator_exact, gap_squared_exact]
  norm_num [alignmentBudget]

theorem residual_characteristic_gates :
    implicitWeightedCap < prime ∧ algebraicCap < prime ∧ slopeCap < prime := by
  rw [parameter_values.2.2.2.2.1]
  norm_num [prime, algebraicCap, slopeCap, seedTotalCap]

def radius6543 : ℝ≥0 := claimedRadius 312843 1048576

theorem radius_numerator_exact : 312843 = 4 * errors + 3 := by
  norm_num [errors]

theorem radius6543_floor :
    ⌊(radius6543 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius6543, claimedRadius, errors, IRSProfile.Index]

theorem radius6543_gap :
    131071 < Fintype.card IRSProfile.Index - errors := by
  norm_num [IRSProfile.Index, errors]

/-- Tight rational upper enclosure of `2^(43/100)`. -/
theorem two_rpow_forty_three_hundred_le :
    (2 : ℝ≥0) ^ ((43 : ℝ) / 100) ≤ (13473 : ℝ≥0) / 10000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (43 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
        (13473 : ℝ≥0) / 10000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((43 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (43 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (13473 : ℝ≥0) / 10000 := hroot

theorem radius6543_power_rational_bound :
    (1 - radius6543) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * (10000 / 13473) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6543, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6543_score :
    (1 - radius6543) ^ IRSProfile.repetitions ≤ claimedError 6543 := by
  have hscale : (10000 : ℝ≥0) / 13473 ≤
      (2 : ℝ≥0) ^ (-((43 : ℝ) / 100)) := by
    calc
      (10000 : ℝ≥0) / 13473 = 1 / ((13473 : ℝ≥0) / 10000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((43 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_forty_three_hundred_le
      _ = (2 : ℝ≥0) ^ (-((43 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6543) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * (10000 / 13473) :=
      radius6543_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) *
        (2 : ℝ≥0) ^ (-((43 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6543 := by
      unfold claimedError
      rw [show -((((6543 : ℕ) : ℝ) / 100)) =
          -((65 : ℕ) : ℝ) + -((43 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research

#print axioms ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research.interpolation_gate
#print axioms ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research.strict_budget
#print axioms ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research.radius6543_score
