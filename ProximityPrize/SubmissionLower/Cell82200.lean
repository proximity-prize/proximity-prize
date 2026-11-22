import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic

set_option Elab.async false
set_option maxRecDepth 12000

namespace ProximityPrize.SubmissionLower.Cell82200

open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal

abbrev p : ℕ := 2894231263655162954
abbrev q : ℕ := 9223372036854557403

theorem larger_radius :
    claimedRadius 336932863 1073741824 < claimedRadius p q := by
  norm_num [claimedRadius]

/-- No fraction with an allowed denominator lies between p/q and the next error cutoff. -/
theorem maximal_in_cell (a b : ℕ) (size : b ≤ 9223372036854775807)
    (below : a * 262144 < 82259 * b) : a * q ≤ p * b := by
  have hb : a * 262144 < 82259 * b := below
  by_contra! above
  have h₁ : (p : ℤ) * b + 1 ≤ (a : ℤ) * q := by exact_mod_cast above
  have h₂ : (a : ℤ) * 262144 + 1 ≤ 82259 * (b : ℤ) := by exact_mod_cast hb
  have join := add_le_add (mul_le_mul_of_nonneg_left h₁ (by decide : (0 : ℤ) ≤ 262144))
    (mul_le_mul_of_nonneg_left h₂ (by decide : (0 : ℤ) ≤ q))
  norm_num [p, q] at join
  omega

/-- A comparison of natural powers gives a rational exponent on the bit scale. -/
private theorem of_cross_power {x : ℝ≥0} {a d : ℕ} (hd : 0 < d)
    (h : x ^ d * 2 ^ a ≤ 1) : x ≤ (2 : ℝ≥0) ^ (-(a : ℝ) / d) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (NNReal.rpow_le_rpow_iff hd').mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ hd'.ne', NNReal.rpow_natCast,
    NNReal.rpow_neg, NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h

/-- Exact spot-check bound at the greatest fraction in this error cell. -/
theorem fine_score :
    (1 - claimedRadius p q) ^ IRSProfile.repetitions ≤ (2 : ℝ≥0) ^ (-((6954 : ℝ) / 100)) := by
  let x : ℝ≥0 := (1 - claimedRadius p q) ^ 128
  have small : claimedRadius p q ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : 1 - claimedRadius p q = (6329140773199394449 : ℝ≥0) / q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [claimedRadius]
  have upper : x * 2 ^ 69 ≤ (687564359377 : ℝ≥0) / 1000000000000 := by
    dsimp only [x]
    rw [diff, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (6329140773199394449 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ≤
      687564359377 * q ^ 128 by decide +kernel)
  change x ≤ _
  rw [← neg_div]
  apply of_cross_power (a := 6954) (d := 100) (by decide)
  calc
    x ^ 100 * 2 ^ 6954 = (x * 2 ^ 69) ^ 100 * 2 ^ 54 := by
      rw [mul_pow, mul_assoc, ← pow_mul (2 : ℝ≥0), ← pow_add]
    _ ≤ ((687564359377 : ℝ≥0) / 1000000000000) ^ 100 * 2 ^ 54 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left' upper _) (by positivity)
    _ ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      exact_mod_cast (show (687564359377 : ℕ) ^ 100 * 2 ^ 54 ≤ 1000000000000 ^ 100 by decide +kernel)

/-- The original and enlarged radius have identical error cutoffs on the fixed domain. -/
theorem extend (h : ProtocolClaim 6954 336932863 1073741824) : ProtocolClaim 6954 p q where
  admissible := by constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    let old := claimedRadius 336932863 1073741824
    let newRadius := claimedRadius p q
    have cell : ⌊newRadius * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
        ⌊old * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ := by
      rw [IRSProfile.card_index]
      norm_num [old, newRadius, claimedRadius]
    have same : ⌊(newRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
        ⌊(old : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ := by exact_mod_cast cell
    change ToyProblem.certifiedGammaError IRSProfile.code newRadius ≤ reductionTarget
    have h' : ToyProblem.certifiedGammaError IRSProfile.code old ≤ reductionTarget := h.reduction
    unfold ToyProblem.certifiedGammaError at h' ⊢
    rwa [mcaError_eq_of_floor_eq (AffineLineGenerator IRSProfile.Field) IRSProfile.code
      newRadius.coe_nonneg old.coe_nonneg same, GrandChallenges.lambda_eq_of_floor_eq cell]
  score := by
    simpa [claimedError] using fine_score

end ProximityPrize.SubmissionLower.Cell82200
