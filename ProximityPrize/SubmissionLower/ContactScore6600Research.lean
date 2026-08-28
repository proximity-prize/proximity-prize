import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.18 candidate

The radius is the top grid point in the `78955`-error cell,
`(4 * 78955 + 3) / 2^20`.  The claimed score `6618` centibits decomposes as
`66 + 18/100`; the fractional part is enclosed by the upper rational
approximation `2^(18/100) = 2^(9/50) ≤ 113289 / 100000`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6600Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6600 : ℝ≥0 := claimedRadius 315823 1048576
def errors6600 : ℕ := 78955
def score6600 : ℕ := 6618

theorem radius_numerator_exact : 315823 = 4 * errors6600 + 3 := by
  norm_num [errors6600]

theorem radius6600_floor :
    ⌊(radius6600 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6600 := by
  norm_num [radius6600, claimedRadius, errors6600, IRSProfile.Index]

theorem radius6600_cell_cross :
    315823 * Fintype.card IRSProfile.Index <
      (errors6600 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_gap :
    131071 < Fintype.card IRSProfile.Index - errors6600 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_admissible :
    radius6600 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6600, claimedRadius, IRSProfile.minRelativeDistance]

/-- Upper, not lower, rational approximation to `2^(18/100) = 2^(9/50)`. -/
theorem two_rpow_eighteen_hundred_le :
    (2 : ℝ≥0) ^ ((18 : ℝ) / 100) ≤ (113289 : ℝ≥0) / 100000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (9 : ℕ)) ^ ((50 : ℝ)⁻¹) ≤ (113289 : ℝ≥0) / 100000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 50)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((18 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (9 : ℕ)) ^ ((50 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num
    _ ≤ (113289 : ℝ≥0) / 100000 := hroot

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6600_power_rational_bound :
    (1 - radius6600) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * ((100000 : ℝ≥0) / 113289) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6600, claimedRadius, IRSProfile.repetitions, div_pow,
    div_le_iff₀]

theorem radius6600_score :
    (1 - radius6600) ^ IRSProfile.repetitions ≤ claimedError score6600 := by
  have hbase : (100000 : ℝ≥0) / 113289 ≤ (2 : ℝ≥0) ^ (-((18 : ℝ) / 100)) := by
    calc
      (100000 : ℝ≥0) / 113289 = 1 / ((113289 : ℝ≥0) / 100000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((18 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_eighteen_hundred_le
      _ = (2 : ℝ≥0) ^ (-((18 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6600) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * ((100000 : ℝ≥0) / 113289) :=
      radius6600_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (2 : ℝ≥0) ^ (-((18 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = claimedError score6600 := by
      unfold claimedError score6600
      rw [show -((((6618 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((18 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6600Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_score
