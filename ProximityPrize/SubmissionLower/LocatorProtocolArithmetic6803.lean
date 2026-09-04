import ProximityPrize.SubmissionLower.LocatorArithmetic

/-!
# Radius and score arithmetic for the 68.03 row

The numerator is the largest dyadic numerator whose radius has floor 80781
on the size-`2^18` IRS domain.  The rational `236/241` separates its exact
128-fold spot-check error from `2^(-68.03)` with an integer-only proof.
-/

namespace ProximityPrize.SubmissionLower.LocatorProtocolArithmetic6803

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

set_option autoImplicit false

def errors : ℕ := 80781
def radiusNumerator : ℕ := 10340095
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]

theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
      IRSProfile.minRelativeDistance]

theorem score_root_integer :
    (2 : ℕ) ^ 3 * 236 ^ 100 ≤ 241 ^ 100 := by
  native_decide

theorem score_radius_integer :
    (23214337 : ℕ) ^ 128 * (2 ^ 68 * 241) ≤
      236 * 33554432 ^ 128 := by
  native_decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0) ^ ((3 : ℝ) / 100) ≤ (241 : ℝ≥0) / 236 := by
  have hroot : ((2 : ℝ≥0) ^ (3 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
      (241 : ℝ≥0) / 236 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0) ^ ((3 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (3 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (236 / 241) := by
  have hsub : (1 - radius : ℝ≥0) = 23214337 / 33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius) ^ 128 ≤
    ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (236 / 241)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius) ^ IRSProfile.repetitions ≤ claimedError 6803 := by
  have hscale : (236 : ℝ≥0) / 241 ≤
      (2 : ℝ≥0) ^ (-((3 : ℝ) / 100)) := by
    calc
      (236 : ℝ≥0) / 241 = 1 / ((241 : ℝ≥0) / 236) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((3 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (236 / 241) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) *
        (2 : ℝ≥0) ^ (-((3 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6803 := by
      unfold claimedError
      rw [show -((((6803 : ℕ) : ℝ) / 100)) =
          -((68 : ℕ) : ℝ) + -((3 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.LocatorProtocolArithmetic6803
