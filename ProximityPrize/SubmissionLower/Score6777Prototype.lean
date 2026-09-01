import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.Score6777Prototype

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radiusNumerator : ℕ := 10307341
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 80526 := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.Index]

theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
      IRSProfile.minRelativeDistance]

theorem score_root_integer :
    (2 : ℕ) ^ 77 * 1252 ^ 100 ≤ 2135 ^ 100 := by
  decide

theorem score_radius_integer :
    (23247091 : ℕ) ^ 128 * (2 ^ 67 * 2135) ≤
      1252 * 33554432 ^ 128 := by
  decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0) ^ ((77 : ℝ) / 100) ≤ (2135 : ℝ≥0) / 1252 := by
  have hroot : ((2 : ℝ≥0) ^ (77 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤
      (2135 : ℝ≥0) / 1252 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0) ^ ((77 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (77 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (1252 / 2135) := by
  have hsub : (1 - radius : ℝ≥0) = 23247091 / 33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius) ^ 128 ≤
    ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (1252 / 2135)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius) ^ IRSProfile.repetitions ≤ claimedError 6777 := by
  have hscale : (1252 : ℝ≥0) / 2135 ≤
      (2 : ℝ≥0) ^ (-((77 : ℝ) / 100)) := by
    calc
      (1252 : ℝ≥0) / 2135 = 1 / ((2135 : ℝ≥0) / 1252) := by
        norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((77 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (1252 / 2135) :=
      radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) *
        (2 : ℝ≥0) ^ (-((77 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6777 := by
      unfold claimedError
      rw [show -((((6777 : ℕ) : ℝ) / 100)) =
          -((67 : ℕ) : ℝ) + -((77 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.Score6777Prototype
