import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.56 candidate

The radius is the top grid point in the `79337`-error cell,
`(4 * 79337 + 3) / 2^20`.  The score proof uses the rational sandwich

`(1-r)^128 <= 2^-66 * 1000/1475 <= 2^(-66.56)`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6656Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6656 : ℝ≥0 := claimedRadius 317351 1048576
def errors6656 : ℕ := 79337
def score6656 : ℕ := 6656

theorem radius_numerator_exact : 317351 = 4 * errors6656 + 3 := by
  norm_num [errors6656]

theorem radius6656_floor :
    ⌊(radius6656 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6656 := by
  norm_num [radius6656, claimedRadius, errors6656, IRSProfile.Index]

theorem radius6656_cell_cross :
    317351 * Fintype.card IRSProfile.Index <
      (errors6656 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6656]

theorem radius6656_gap :
    131071 < Fintype.card IRSProfile.Index - errors6656 := by
  norm_num [IRSProfile.Index, errors6656]

theorem radius6656_admissible :
    radius6656 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6656, claimedRadius, IRSProfile.minRelativeDistance]

/-- Rational upper enclosure of `2^(56/100)`. -/
theorem two_rpow_fifty_six_hundred_le :
    (2 : ℝ≥0) ^ ((56 : ℝ) / 100) ≤ (1475 : ℝ≥0) / 1000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (56 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
        (1475 : ℝ≥0) / 1000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((56 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (56 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (1475 : ℝ≥0) / 1000 := hroot

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6656_power_rational_bound :
    (1 - radius6656) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (1000 / 1475) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6656, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6656_score :
    (1 - radius6656) ^ IRSProfile.repetitions ≤ claimedError score6656 := by
  have hscale : (1000 : ℝ≥0) / 1475 ≤
      (2 : ℝ≥0) ^ (-((56 : ℝ) / 100)) := by
    calc
      (1000 : ℝ≥0) / 1475 = 1 / ((1475 : ℝ≥0) / 1000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((56 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fifty_six_hundred_le
      _ = (2 : ℝ≥0) ^ (-((56 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6656) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (1000 / 1475) :=
      radius6656_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((56 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6656 := by
      unfold claimedError score6656
      rw [show -((((6656 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((56 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6656Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_cell_cross
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_gap
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.two_rpow_fifty_six_hundred_le
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6656Research.radius6656_score
