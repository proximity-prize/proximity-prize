import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.36 candidate

The radius is the top grid point in the `79135`-error cell,
`(4 * 79135 + 3) / 2^20`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6600Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6600 : ℝ≥0 := claimedRadius 316543 1048576
def errors6600 : ℕ := 79135
def score6600 : ℕ := 6636

theorem radius_numerator_exact : 316543 = 4 * errors6600 + 3 := by
  norm_num [errors6600]

theorem radius6600_floor :
    ⌊(radius6600 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6600 := by
  norm_num [radius6600, claimedRadius, errors6600, IRSProfile.Index]

theorem radius6600_cell_cross :
    316543 * Fintype.card IRSProfile.Index <
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

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6600_power_rational_bound :
    (1 - radius6600) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        ((1000000000 : ℝ≥0) / 1006955551) ^ (36 : ℕ) := by
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
      ((1000000000 : ℝ≥0) / 1006955551) ^ (36 : ℕ) ≤
        (2 : ℝ≥0) ^ (-((36 : ℝ) / 100)) := by
    calc
      _ ≤ ((2 : ℝ≥0) ^ (-((1 : ℝ) / 100))) ^ (36 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hbase 36
      _ = (2 : ℝ≥0) ^ (-((36 : ℝ) / 100)) := by
        rw [← NNReal.rpow_natCast (((2 : ℝ≥0) ^ (-((1 : ℝ) / 100)))) 36,
          ← NNReal.rpow_mul]
        norm_num
  calc
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        ((1000000000 : ℝ≥0) / 1006955551) ^ (36 : ℕ) :=
      radius6600_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((36 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6600 := by
      unfold claimedError score6600
      rw [show -((((6636 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((36 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6600Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_score
