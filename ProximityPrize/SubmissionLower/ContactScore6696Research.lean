import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.96 candidate

The radius is the top grid point in the `79730`-error cell,
`(4 * 79730 + 3) / 2^20`.  The score proof uses the rational sandwich

`(1-r)^128 <= 2^-66 * 19/37 <= 2^(-66.96)`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6696Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6696 : ℝ≥0 := claimedRadius 318923 1048576
def errors6696 : ℕ := 79730
def score6696 : ℕ := 6696

theorem radius_numerator_exact : 318923 = 4 * errors6696 + 3 := by
  norm_num [errors6696]

theorem radius6696_floor :
    ⌊(radius6696 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6696 := by
  norm_num [radius6696, claimedRadius, errors6696, IRSProfile.Index]

theorem radius6696_cell_cross :
    318923 * Fintype.card IRSProfile.Index <
      (errors6696 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6696]

theorem radius6696_gap :
    131071 < Fintype.card IRSProfile.Index - errors6696 := by
  norm_num [IRSProfile.Index, errors6696]

theorem radius6696_admissible :
    radius6696 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6696, claimedRadius, IRSProfile.minRelativeDistance]

/-- Rational upper enclosure of `2^(96/100)`. -/
theorem two_rpow_ninety_six_hundred_le :
    (2 : ℝ≥0) ^ ((96 : ℝ) / 100) ≤ (37 : ℝ≥0) / 19 := by
  have hroot :
      ((2 : ℝ≥0) ^ (24 : ℕ)) ^ ((25 : ℝ)⁻¹) ≤
        (37 : ℝ≥0) / 19 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 25)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((96 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (24 : ℕ)) ^ ((25 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (37 : ℝ≥0) / 19 := hroot

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6696_power_rational_bound :
    (1 - radius6696) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (19 / 37) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6696, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6696_score :
    (1 - radius6696) ^ IRSProfile.repetitions ≤ claimedError score6696 := by
  have hscale : (19 : ℝ≥0) / 37 ≤
      (2 : ℝ≥0) ^ (-((96 : ℝ) / 100)) := by
    calc
      (19 : ℝ≥0) / 37 = 1 / ((37 : ℝ≥0) / 19) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((96 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_ninety_six_hundred_le
      _ = (2 : ℝ≥0) ^ (-((96 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6696) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (19 / 37) :=
      radius6696_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((96 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6696 := by
      unfold claimedError score6696
      rw [show -((((6696 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((96 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6696Research
