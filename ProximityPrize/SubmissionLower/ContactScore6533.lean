import ProximityPrize.SubmissionLower.ContactParameters6533

/-!
# Exact radius and score arithmetic for the 65.67-bit contact candidate

The radius is the top grid point in the `78455`-error cell,
`(4 * 78455 + 3) / 2^20`.  The score proof uses the exact rational sandwich

`(1-r)^128 ≤ 2^-65 * 6285/10000 ≤ 2^(-65.67)`.

No alignment or counting theorem is assumed here.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6533

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6533 : ℝ≥0 := claimedRadius 313823 1048576
def errors6533 : ℕ := 78455
def score6533 : ℕ := 6567

theorem radius_numerator_exact : 313823 = 4 * errors6533 + 3 := by
  norm_num [errors6533]

theorem radius6533_floor :
    ⌊(radius6533 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6533 := by
  norm_num [radius6533, claimedRadius, errors6533, IRSProfile.Index]

theorem radius6533_cell_cross :
    313823 * Fintype.card IRSProfile.Index <
      (errors6533 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6533]

theorem radius6533_gap :
    131071 < Fintype.card IRSProfile.Index - errors6533 := by
  norm_num [IRSProfile.Index, errors6533]

theorem radius6533_admissible :
    radius6533 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6533, claimedRadius, IRSProfile.minRelativeDistance]

/-- Exact upper rational approximation needed for the `0.67` fractional
score bit: `2^(67/100) ≤ 10000/6285`. -/
theorem two_rpow_sixty_seven_hundred_le :
    (2 : ℝ≥0) ^ ((67 : ℝ) / 100) ≤ (10000 : ℝ≥0) / 6285 := by
  have hroot :
      ((2 : ℝ≥0) ^ (67 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
        (10000 : ℝ≥0) / 6285 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((67 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (67 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (10000 : ℝ≥0) / 6285 := hroot

/-- Exact 128th-power rational comparison at the claimed radius. -/
theorem radius6533_power_rational_bound :
    (1 - radius6533) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * (6285 / 10000) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6533, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6533_score :
    (1 - radius6533) ^ IRSProfile.repetitions ≤ claimedError score6533 := by
  have hscale :
      (6285 : ℝ≥0) / 10000 ≤ (2 : ℝ≥0) ^ (-((67 : ℝ) / 100)) := by
    calc
      (6285 : ℝ≥0) / 10000 = 1 / ((10000 : ℝ≥0) / 6285) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((67 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity)
          two_rpow_sixty_seven_hundred_le
      _ = (2 : ℝ≥0) ^ (-((67 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6533) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * (6285 / 10000) :=
      radius6533_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) *
        (2 : ℝ≥0) ^ (-((67 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError score6533 := by
      unfold claimedError score6533
      rw [show -((((6567 : ℕ) : ℝ) / 100)) =
          -((65 : ℕ) : ℝ) + -((67 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6533

#print axioms ProximityPrize.SubmissionLower.ContactScore6533.radius6533_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6533.radius6533_cell_cross
#print axioms ProximityPrize.SubmissionLower.ContactScore6533.radius6533_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6533.two_rpow_sixty_seven_hundred_le
#print axioms ProximityPrize.SubmissionLower.ContactScore6533.radius6533_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6533.radius6533_score
