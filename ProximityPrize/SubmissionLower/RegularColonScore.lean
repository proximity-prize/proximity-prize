import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.RegularColonScore
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def errors : ℕ := 80112
def radiusNumerator : ℕ := 10254463
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]
theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer : (2 : ℕ)^7 * 790^20 ≤ 1007^20 := by decide
theorem score_radius_integer :
    (23299969 : ℕ)^128 * (2^67 * 1007) ≤ 790 * 33554432^128 := by decide
theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((7 : ℝ)/20) ≤ (1007 : ℝ≥0)/790 := by
  have hroot : ((2 : ℝ≥0)^(7 : ℕ))^((20 : ℝ)⁻¹) ≤ (1007 : ℝ≥0)/790 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 20)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((7 : ℝ)/20) = ((2 : ℝ≥0)^(7 : ℕ))^((20 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot
theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ)) * (790/1007) := by
  have hsub : (1 - radius : ℝ≥0) = 23299969/33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (790/1007)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6735 := by
  have hscale : (790 : ℝ≥0)/1007 ≤ (2 : ℝ≥0)^(-((7 : ℝ)/20)) := by
    calc
      (790 : ℝ≥0)/1007 = 1/((1007 : ℝ≥0)/790) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((7 : ℝ)/20)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ)) * (790/1007) := radius_power_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((7 : ℝ)/20)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6735 := by
      unfold claimedError
      rw [show -((((6735 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((7 : ℝ)/20) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.RegularColonScore
