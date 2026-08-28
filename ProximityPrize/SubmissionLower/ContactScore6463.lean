import ProximityPrize.SubmissionLower.ContactParameters6463

/-!
# Exact radius and score arithmetic for the 64.63-bit contact row

The radius is the top grid point in the `77416`-error cell,
`(4 * 77416 + 3) / 2^20`.  The score proof uses the exact rational sandwich

`(1-r)^128 ≤ 2^-64 * 20/31 ≤ 2^(-64.63)`.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6463

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6463 : ℝ≥0 := claimedRadius 309667 1048576
def errors6463 : ℕ := 77416

theorem radius_numerator_exact : 309667 = 4 * errors6463 + 3 := by
  norm_num [errors6463]

theorem radius6463_floor :
    ⌊(radius6463 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6463 := by
  norm_num [radius6463, claimedRadius, errors6463, IRSProfile.Index]

theorem radius6463_cell_cross :
    309667 * Fintype.card IRSProfile.Index <
      (errors6463 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6463]

theorem radius6463_gap :
    131071 < Fintype.card IRSProfile.Index - errors6463 := by
  norm_num [IRSProfile.Index, errors6463]

theorem radius6463_admissible :
    radius6463 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6463, claimedRadius, IRSProfile.minRelativeDistance]

theorem two_rpow_sixty_three_hundred_le :
    (2 : ℝ≥0) ^ ((63 : ℝ) / 100) ≤ (31 : ℝ≥0) / 20 := by
  have hroot :
      ((2 : ℝ≥0) ^ (63 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
        (31 : ℝ≥0) / 20 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((63 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (63 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (31 : ℝ≥0) / 20 := hroot

theorem radius6463_power_rational_bound :
    (1 - radius6463) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (20 / 31) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6463, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6463_score :
    (1 - radius6463) ^ IRSProfile.repetitions ≤ claimedError 6463 := by
  have hscale :
      (20 : ℝ≥0) / 31 ≤ (2 : ℝ≥0) ^ (-((63 : ℝ) / 100)) := by
    calc
      (20 : ℝ≥0) / 31 = 1 / ((31 : ℝ≥0) / 20) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((63 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity)
          two_rpow_sixty_three_hundred_le
      _ = (2 : ℝ≥0) ^ (-((63 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius6463) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (20 / 31) :=
      radius6463_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
        (2 : ℝ≥0) ^ (-((63 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6463 := by
      unfold claimedError
      rw [show -((((6463 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + -((63 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.ContactScore6463

#print axioms ProximityPrize.SubmissionLower.ContactScore6463.radius6463_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6463.radius6463_cell_cross
#print axioms ProximityPrize.SubmissionLower.ContactScore6463.radius6463_gap
#print axioms ProximityPrize.SubmissionLower.ContactScore6463.radius6463_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6463.radius6463_score
