import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.74 candidate

The radius is the top grid point in the `79514`-error cell,
`(4 * 79514 + 3) / 2^20`.  The fractional score comparison uses the exact
rational sandwich

`(1-r)^128 <= 2^-66 * (1000/1671) <= 2^(-66.74)`.

No counting or geometric premise occurs in this module.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6630Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6630 : ℝ≥0 := claimedRadius 318059 1048576
def errors6630 : ℕ := 79514
def score6630 : ℕ := 6674

theorem radius_numerator_exact : 318059 = 4 * errors6630 + 3 := by
  norm_num [errors6630]

theorem radius6630_floor :
    ⌊(radius6630 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6630 := by
  norm_num [radius6630, claimedRadius, errors6630, IRSProfile.Index]

theorem radius6630_cell_cross :
    318059 * Fintype.card IRSProfile.Index <
      (errors6630 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_gap :
    131071 < Fintype.card IRSProfile.Index - errors6630 := by
  norm_num [IRSProfile.Index, errors6630]

theorem radius6630_admissible :
    radius6630 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6630, claimedRadius, IRSProfile.minRelativeDistance]

/-- Exact rational upper approximation `2^(37/50) <= 1671/1000`. -/
theorem two_rpow_37_fiftieths_le :
    (2 : ℝ≥0) ^ ((37 : ℝ) / 50) ≤ (1671 : ℝ≥0) / 1000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (37 : ℕ)) ^ ((50 : ℝ)⁻¹) ≤
        (1671 : ℝ≥0) / 1000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 50)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((37 : ℝ) / 50) =
        ((2 : ℝ≥0) ^ (37 : ℕ)) ^ ((50 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (1671 : ℝ≥0) / 1000 := hroot

/-- Exact 128th-power rational comparison at the claimed radius. -/
theorem radius6630_power_rational_bound :
    (1 - radius6630) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (1000 / 1671) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6630, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6630_score :
    (1 - radius6630) ^ IRSProfile.repetitions ≤ claimedError score6630 := by
  have hscale :
      (1000 : ℝ≥0) / 1671 ≤ (2 : ℝ≥0) ^ (-((37 : ℝ) / 50)) := by
    calc
      (1000 : ℝ≥0) / 1671 = 1 / ((1671 : ℝ≥0) / 1000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((37 : ℝ) / 50)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_37_fiftieths_le
      _ = (2 : ℝ≥0) ^ (-((37 : ℝ) / 50)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6630) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) * (1000 / 1671) :=
      radius6630_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (66 : ℕ)) *
        (2 : ℝ≥0) ^ (-((37 : ℝ) / 50)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6630 := by
      unfold claimedError score6630
      rw [show -((((6674 : ℕ) : ℝ) / 100)) =
          -((66 : ℕ) : ℝ) + -((37 : ℝ) / 50) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6630Research
