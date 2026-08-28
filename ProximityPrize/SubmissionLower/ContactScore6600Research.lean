import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.25 candidate
-/

namespace ProximityPrize.SubmissionLower.ContactScore6600Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6600 : ℝ≥0 := claimedRadius 316131 1048576
def errors6600 : ℕ := 79032
def score6600 : ℕ := 6625

theorem radius_numerator_exact : 316131 = 4 * errors6600 + 3 := by
  norm_num [errors6600]

theorem radius6600_floor :
    ⌊(radius6600 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6600 := by
  norm_num [radius6600, claimedRadius, errors6600, IRSProfile.Index]

theorem radius6600_cell_cross :
    316131 * Fintype.card IRSProfile.Index <
      (errors6600 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_gap :
    131071 < Fintype.card IRSProfile.Index - errors6600 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_admissible :
    radius6600 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6600, claimedRadius, IRSProfile.minRelativeDistance]

theorem two_rpow_one_hundred_le :
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) ≤
      (1006955551 : ℝ≥0) / 1000000000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
        (1006955551 : ℝ≥0) / 1000000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (1006955551 : ℝ≥0) / 1000000000 := hroot

theorem radius6600_power_rational_bound :
    (1 - radius6600) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        ((1000000000 : ℝ≥0) / 1006955551) ^ (25 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6600, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6600_score :
    (1 - radius6600) ^ IRSProfile.repetitions ≤ claimedError score6600 := by
  have hbase : (1000000000 : ℝ≥0) / 1006955551 ≤
      (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
    calc
      (1000000000 : ℝ≥0) / 1006955551 =
          1 / ((1006955551 : ℝ≥0) / 1000000000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((1 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity)
          two_rpow_one_hundred_le
      _ = (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  have hscale :
      ((1000000000 : ℝ≥0) / 1006955551) ^ (25 : ℕ) ≤
        (2 : ℝ≥0) ^ (-((25 : ℝ) / 100)) := by
    calc
      _ ≤ ((2 : ℝ≥0) ^ (-((1 : ℝ) / 100))) ^ (25 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hbase 25
      _ = (2 : ℝ≥0) ^ (-((25 : ℝ) / 100)) := by
        rw [← NNReal.rpow_natCast (((2 : ℝ≥0) ^ (-((1 : ℝ) / 100)))) 25,
          ← NNReal.rpow_mul]
        norm_num
  calc
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        ((1000000000 : ℝ≥0) / 1006955551) ^ (25 : ℕ) :=
      radius6600_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((25 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6600 := by
      unfold claimedError score6600
      rw [show -((((6625 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((25 : ℝ) / 100) by norm_num,
        NNReal.rpow_add two_ne_zero, NNReal.rpow_neg,
        NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6600Research
