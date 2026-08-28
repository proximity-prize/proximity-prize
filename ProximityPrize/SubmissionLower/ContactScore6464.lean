import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 64.64-bit contact row

The radius is the top grid point in the `77424`-error cell,
`(4 * 77424 + 3) / 2^20`.  The score proof uses the exact rational sandwich

`(1-r)^128 ≤ 2^-64 * 1000/1559 ≤ 2^(-64.64)`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6464

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6464 : ℝ≥0 := claimedRadius 309699 1048576
def errors6464 : ℕ := 77424

theorem radius_numerator_exact : 309699 = 4 * errors6464 + 3 := by
  norm_num [errors6464]

theorem radius6464_floor :
    ⌊(radius6464 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6464 := by
  norm_num [radius6464, claimedRadius, errors6464, IRSProfile.Index]

theorem radius6464_cell_cross :
    309699 * Fintype.card IRSProfile.Index <
      (errors6464 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6464]

theorem radius6464_gap :
    131071 < Fintype.card IRSProfile.Index - errors6464 := by
  norm_num [IRSProfile.Index, errors6464]

theorem radius6464_admissible :
    radius6464 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6464, claimedRadius, IRSProfile.minRelativeDistance]

/-- Rational upper enclosure of `2^(64/100)`. -/
theorem two_rpow_sixty_four_hundred_le :
    (2 : ℝ≥0) ^ ((64 : ℝ) / 100) ≤ (1559 : ℝ≥0) / 1000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (64 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ (1559 : ℝ≥0) / 1000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((64 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (64 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (1559 : ℝ≥0) / 1000 := hroot

theorem radius6464_power_rational_bound :
    (1 - radius6464) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (1000 / 1559) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6464, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6464_score :
    (1 - radius6464) ^ IRSProfile.repetitions ≤ claimedError 6464 := by
  have hscale : (1000 : ℝ≥0) / 1559 ≤
      (2 : ℝ≥0) ^ (-((64 : ℝ) / 100)) := by
    calc
      (1000 : ℝ≥0) / 1559 = 1 / ((1559 : ℝ≥0) / 1000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((64 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_sixty_four_hundred_le
      _ = (2 : ℝ≥0) ^ (-((64 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6464) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (1000 / 1559) :=
      radius6464_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
        (2 : ℝ≥0) ^ (-((64 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6464 := by
      unfold claimedError
      rw [show -((((6464 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + -((64 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6464

#print axioms ProximityPrize.SubmissionLower.ContactScore6464.radius6464_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6464.radius6464_cell_cross
#print axioms ProximityPrize.SubmissionLower.ContactScore6464.radius6464_gap
#print axioms ProximityPrize.SubmissionLower.ContactScore6464.radius6464_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6464.radius6464_score
