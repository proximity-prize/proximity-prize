/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.RadiusCell

namespace ProximityPrize.SubmissionLower.Radius81185

open ProximityPrize.Benchmark
open scoped NNReal

abbrev numerator : ℕ := 2856478432403892112
abbrev denominator : ℕ := 9223372036854702705

theorem radius_lt : claimedRadius 332537855 1073741824 < claimedRadius numerator denominator := by
  rw [claimedRadius, claimedRadius, div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num

theorem spot_check_lt :
    (1 - claimedRadius numerator denominator)^IRSProfile.repetitions <
    (1 - claimedRadius 332537855 1073741824)^IRSProfile.repetitions := by
  have hi : claimedRadius numerator denominator ≤ 1 := by
    rw [claimedRadius, div_le_one (by positivity)]
    norm_num
  have lo := radius_lt.le.trans hi
  apply pow_lt_pow_left₀ _ (by positivity) (by decide)
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub hi, NNReal.coe_sub lo]
  exact sub_lt_sub_left (NNReal.coe_lt_coe.mpr radius_lt) _

/-- The two radii contain precisely the same integer Hamming distances. -/
theorem improve (h : ProtocolClaim 6844 332537855 1073741824) :
    ProtocolClaim 6844 numerator denominator := by
  apply RadiusCell.extend h
  · constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  · exact radius_lt.le
  · rw [IRSProfile.card_index]
    norm_num [claimedRadius]

/-- Largest legal fraction strictly below the first excluded Hamming distance. -/
theorem maximal {a b : ℕ} (hb : 0 < b) (cap : b ≤ 2^63-1)
    (within : claimedRadius a b < 40593 / 131072) :
    claimedRadius a b ≤ claimedRadius numerator denominator := by
  have hb' : 0 < (b : ℝ≥0) := by exact_mod_cast hb
  have small : a * 131072 < 40593 * b := by
    unfold claimedRadius at within
    exact_mod_cast (div_lt_div_iff₀ hb' (by positivity)).mp within
  have le : a * denominator ≤ numerator * b := by
    change a * 9223372036854702705 ≤ 2856478432403892112 * b
    by_contra! larger
    have one : 1 ≤ 40593 * b - 131072 * a := by omega
    have extra : 1 ≤ 9223372036854702705 * a - 2856478432403892112 * b := by omega
    have equation :
        9223372036854702705 * (40593 * b - 131072 * a) +
        131072 * (9223372036854702705 * a - 2856478432403892112 * b) = b := by
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    omega
  exact (div_le_div_iff₀ hb' (by positivity)).mpr (by exact_mod_cast le)

end ProximityPrize.SubmissionLower.Radius81185
