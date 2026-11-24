import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic

set_option Elab.async false
set_option maxRecDepth 12000

namespace ProximityPrize.SubmissionLower.Front6961Radius

open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal

abbrev p : ℕ := 337210382
abbrev q : ℕ := 1073741824

private theorem of_cross_power {x : ℝ≥0} {a d : ℕ} (hd : 0 < d)
    (h : x ^ d * 2 ^ a ≤ 1) : x ≤ (2 : ℝ≥0) ^ (-(a : ℝ) / d) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (NNReal.rpow_le_rpow_iff hd').mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ hd'.ne', NNReal.rpow_natCast,
    NNReal.rpow_neg, NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h

/-- Exact spot-check bound at the 69.61 dyadic radius 337210382 / 2^30. -/
theorem dyadic_score :
    (1 - claimedRadius 337210382 1073741824) ^ IRSProfile.repetitions ≤ (2 : ℝ≥0) ^ (-((6961 : ℝ) / 100)) := by
  let x : ℝ≥0 := (1 - claimedRadius 337210382 1073741824) ^ 128
  have small : claimedRadius 337210382 1073741824 ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : 1 - claimedRadius 337210382 1073741824 = (736531442 : ℝ≥0) / 1073741824 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [claimedRadius]
  have upper : x * 2 ^ 69 ≤ (655196602709 : ℝ≥0) / 1000000000000 := by
    dsimp only [x]
    rw [diff, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (736531442 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ≤
      655196602709 * 1073741824 ^ 128 by decide +kernel)
  change x ≤ _
  rw [← neg_div]
  apply of_cross_power (a := 6961) (d := 100) (by decide)
  calc
    x ^ 100 * 2 ^ 6961 = (x * 2 ^ 69) ^ 100 * 2 ^ 61 := by
      rw [mul_pow, mul_assoc, ← pow_mul (2 : ℝ≥0), ← pow_add]
    _ ≤ ((655196602709 : ℝ≥0) / 1000000000000) ^ 100 * 2 ^ 61 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left' upper _) (by positivity)
    _ ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      exact_mod_cast (show (655196602709 : ℕ) ^ 100 * 2 ^ 61 ≤ 1000000000000 ^ 100 by decide +kernel)

end ProximityPrize.SubmissionLower.Front6961Radius
