/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.RadiusCell

namespace ProximityPrize.SubmissionLower.Radius81184

open ProximityPrize.Benchmark
open scoped NNReal

abbrev numerator : ℕ := 2856443248031796021
abbrev denominator : ℕ := 9223372036854679265

theorem radius_lt : claimedRadius 332533759 1073741824 < claimedRadius numerator denominator := by
  rw [claimedRadius, claimedRadius, div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num

theorem spot_check_lt :
    (1 - claimedRadius numerator denominator)^IRSProfile.repetitions <
    (1 - claimedRadius 332533759 1073741824)^IRSProfile.repetitions := by
  have hi : claimedRadius numerator denominator ≤ 1 := by
    rw [claimedRadius, div_le_one (by positivity)]
    norm_num
  have lo := radius_lt.le.trans hi
  apply pow_lt_pow_left₀ _ (by positivity) (by decide)
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub hi, NNReal.coe_sub lo]
  exact sub_lt_sub_left (NNReal.coe_lt_coe.mpr radius_lt) _

/-- The two radii contain precisely the same integer Hamming distances. -/
theorem improve (h : ProtocolClaim 6844 332533759 1073741824) :
    ProtocolClaim 6844 numerator denominator := by
  apply RadiusCell.extend h
  · constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  · exact radius_lt.le
  · rw [IRSProfile.card_index]
    norm_num [claimedRadius]

/-- Largest legal fraction strictly below the first excluded Hamming distance. -/
theorem maximal {a b : ℕ} (hb : 0 < b) (cap : b ≤ 2^63-1)
    (within : claimedRadius a b < 81185 / 262144) :
    claimedRadius a b ≤ claimedRadius numerator denominator := by
  have hb' : 0 < (b : ℝ≥0) := by exact_mod_cast hb
  have small : a * 262144 < 81185 * b := by
    unfold claimedRadius at within
    exact_mod_cast (div_lt_div_iff₀ hb' (by positivity)).mp within
  have le : a * denominator ≤ numerator * b := by
    change a * 9223372036854679265 ≤ 2856443248031796021 * b
    by_contra! larger
    have one : 1 ≤ 81185 * b - 262144 * a := by omega
    have extra : 1 ≤ 9223372036854679265 * a - 2856443248031796021 * b := by omega
    have equation :
        9223372036854679265 * (81185 * b - 262144 * a) +
        262144 * (9223372036854679265 * a - 2856443248031796021 * b) = b := by
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    omega
  exact (div_le_div_iff₀ hb' (by positivity)).mpr (by exact_mod_cast le)

end ProximityPrize.SubmissionLower.Radius81184
