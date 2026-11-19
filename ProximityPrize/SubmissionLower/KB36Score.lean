/- Apache-2.0. Bome2017. Exact score of the 68.36 radius. -/
import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.KB36Integers
namespace ProximityPrize.SubmissionLower.JointProtocol6836
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def errors : ℕ := 81105
def mcaBudget : ℕ := 274980640798883310
def radiusNumerator : ℕ := 332210175
def radiusDenominator : ℕ := 1073741824
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

theorem radius_admissible : radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]

theorem radius_cell :
    (radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ) < ((errors + 1 : ℕ) : ℝ) := by
  rw [IRSProfile.card_index]
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator, errors]

private theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((36 : ℝ) / 100) ≤ (128342590 : ℝ≥0) / 100000000 := by
  have hroot : ((2 : ℝ≥0)^(36 : ℕ))^((100 : ℝ)⁻¹) ≤
      (128342590 : ℝ≥0) / 100000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast Koala6836.ProtocolInt.score_root_integer
  calc
    (2 : ℝ≥0)^((36 : ℝ) / 100) = ((2 : ℝ≥0)^(36 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

private theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 128342590) := by
  have hsub : (1 - radius : ℝ≥0) = 741531649 / 1073741824 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 128342590)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast Koala6836.ProtocolInt.score_radius_integer

theorem score_target_le : (1 - radius)^IRSProfile.repetitions ≤ claimedError 6836 := by
  have hscale : (100000000 : ℝ≥0) / 128342590 ≤ (2 : ℝ≥0)^(-((36 : ℝ) / 100)) := by
    calc
      (100000000 : ℝ≥0) / 128342590 = 1 / ((128342590 : ℝ≥0) / 100000000) := by
        norm_num
      _ ≤ 1 / ((2 : ℝ≥0)^((36 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2^(68 : ℕ)) * (100000000 / 128342590) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2^(68 : ℕ)) * (2 : ℝ≥0)^(-((36 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6836 := by
      unfold claimedError
      rw [show -((((6836 : ℕ) : ℝ) / 100)) =
          -((68 : ℕ) : ℝ) + -((36 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

#print axioms score_target_le
end
end ProximityPrize.SubmissionLower.JointProtocol6836
