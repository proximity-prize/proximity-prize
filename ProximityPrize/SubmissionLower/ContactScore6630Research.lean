import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.75 candidate
-/

namespace ProximityPrize.SubmissionLower.ContactScore6630Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6630 : ℝ≥0 := claimedRadius 318087 1048576
def errors6630 : ℕ := 79521
def score6630 : ℕ := 6675

theorem radius_numerator_exact : 318087 = 4 * errors6630 + 3 := by
  norm_num [errors6630]

theorem radius6630_floor :
    ⌊(radius6630 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6630 := by
  norm_num [radius6630, claimedRadius, errors6630, IRSProfile.Index]

theorem radius6630_cell_cross :
    318087 * Fintype.card IRSProfile.Index <
      (errors6630 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_gap :
    131071 < Fintype.card IRSProfile.Index - errors6630 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_admissible :
    radius6630 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6630, claimedRadius, IRSProfile.minRelativeDistance]

theorem two_rpow_three_fourths_le :
    (1681 : ℝ≥0) / 1000 ≤ (2 : ℝ≥0) ^ ((75 : ℝ) / 100) := by
  have hpow : ((1681 : ℝ≥0) / 1000) ^ (4 : ℕ) ≤ 8 := by
    norm_num [div_pow, le_div_iff₀]
  calc
    (1681 : ℝ≥0) / 1000 = (((1681 : ℝ≥0) / 1000) ^ (4 : ℕ)) ^ ((4 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
      norm_num
    _ ≤ (8 : ℝ≥0) ^ ((4 : ℝ)⁻¹) := by
      exact NNReal.rpow_le_rpow hpow (by norm_num)
    _ = (2 : ℝ≥0) ^ ((75 : ℝ) / 100) := by
      rw [show (8 : ℝ≥0) = (2 : ℝ≥0) ^ (3 : ℕ) by norm_num,
        ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
      norm_num

theorem radius6630_power_rational_bound :
    (1 - radius6630) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        ((1000 : ℝ≥0) / 1681) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6630, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6630_score :
    (1 - radius6630) ^ IRSProfile.repetitions ≤ claimedError score6630 := by
  have hbase : (1000 : ℝ≥0) / 1681 ≤ (2 : ℝ≥0) ^ (-((75 : ℝ) / 100)) := by
    calc
      (1000 : ℝ≥0) / 1681 = 1 / ((1681 : ℝ≥0) / 1000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((75 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_three_fourths_le
      _ = (2 : ℝ≥0) ^ (-((75 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * ((1000 : ℝ≥0) / 1681) :=
      radius6630_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (2 : ℝ≥0) ^ (-((75 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = claimedError score6630 := by
      unfold claimedError score6630
      rw [show -((((6675 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((75 : ℝ) / 100) by norm_num,
        NNReal.rpow_add two_ne_zero, NNReal.rpow_neg,
        NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6630Research
