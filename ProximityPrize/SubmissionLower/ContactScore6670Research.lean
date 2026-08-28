import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.70 candidate

The radius is the top grid point in the `79476`-error cell,
`(4 * 79476 + 3) / 2^20`.  The score proof uses the rational sandwich

`(1-r)^128 <= 2^-66 * 8/13 <= 2^(-66.70)`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6670Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6670 : ℝ≥0 := claimedRadius 317907 1048576
def errors6670 : ℕ := 79476
def score6670 : ℕ := 6670

theorem radius_numerator_exact : 317907 = 4 * errors6670 + 3 := by
  norm_num [errors6670]

theorem radius6670_floor :
    ⌊(radius6670 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6670 := by
  norm_num [radius6670, claimedRadius, errors6670, IRSProfile.Index]

theorem radius6670_cell_cross :
    317907 * Fintype.card IRSProfile.Index <
      (errors6670 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6670]

theorem radius6670_gap :
    131071 < Fintype.card IRSProfile.Index - errors6670 := by
  norm_num [IRSProfile.Index, errors6670]

theorem radius6670_admissible :
    radius6670 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6670, claimedRadius, IRSProfile.minRelativeDistance]

/-- Rational upper enclosure of `2^(70/100)`. -/
theorem two_rpow_seventy_hundred_le :
    (2 : ℝ≥0) ^ ((70 : ℝ) / 100) ≤ (13 : ℝ≥0) / 8 := by
  have hroot :
      ((2 : ℝ≥0) ^ (7 : ℕ)) ^ ((10 : ℝ)⁻¹) ≤
        (13 : ℝ≥0) / 8 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 10)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((70 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (7 : ℕ)) ^ ((10 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (13 : ℝ≥0) / 8 := hroot

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6670_power_rational_bound :
    (1 - radius6670) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (8 / 13) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6670, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6670_score :
    (1 - radius6670) ^ IRSProfile.repetitions ≤ claimedError score6670 := by
  have hscale : (8 : ℝ≥0) / 13 ≤
      (2 : ℝ≥0) ^ (-((70 : ℝ) / 100)) := by
    calc
      (8 : ℝ≥0) / 13 = 1 / ((13 : ℝ≥0) / 8) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((70 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_seventy_hundred_le
      _ = (2 : ℝ≥0) ^ (-((70 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6670) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (8 / 13) :=
      radius6670_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((70 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6670 := by
      unfold claimedError score6670
      rw [show -((((6670 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((70 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6670Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_cell_cross
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_gap
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.two_rpow_seventy_hundred_le
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6670Research.radius6670_score
