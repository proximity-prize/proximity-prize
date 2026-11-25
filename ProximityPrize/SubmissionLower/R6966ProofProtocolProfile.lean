import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.ProtocolProfile
open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal
abbrev p : ℕ := 2898347835189620169
abbrev q : ℕ := 9223372036854760969
abbrev agreement : ℕ := 179769
abbrev listCap : ℕ := 46614219476138
abbrev scalarCap : ℕ := 274934113891918949

private theorem of_cross_power {x : ℝ≥0} {a d : ℕ} (hd : 0 < d)
    (h : x ^ d * 2 ^ a ≤ 1) : x ≤ (2 : ℝ≥0) ^ (-(a : ℝ) / d) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (NNReal.rpow_le_rpow_iff hd').mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ hd'.ne', NNReal.rpow_natCast,
    NNReal.rpow_neg, NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h
theorem score :
    (1 - claimedRadius p q) ^ IRSProfile.repetitions ≤ (2 : ℝ≥0) ^ (-((6966 : ℝ) / 100)) := by
  let x : ℝ≥0 := (1 - claimedRadius p q) ^ 128
  have small : claimedRadius p q ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : 1 - claimedRadius p q = (6325024201665140800 : ℝ≥0) / q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [claimedRadius]
  have upper : x * 2 ^ 69 ≤ (632623313043 : ℝ≥0) / 1000000000000 := by
    dsimp only [x]
    rw [diff, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (6325024201665140800 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ≤
      632623313043 * q ^ 128 by decide +kernel)
  change x ≤ _
  rw [← neg_div]
  apply of_cross_power (a := 6966) (d := 100) (by decide)
  calc
    x ^ 100 * 2 ^ 6966 = (x * 2 ^ 69) ^ 100 * 2 ^ 66 := by
      rw [mul_pow, mul_assoc, ← pow_mul (2 : ℝ≥0), ← pow_add]
    _ ≤ ((632623313043 : ℝ≥0) / 1000000000000) ^ 100 * 2 ^ 66 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left' upper _) (by positivity)
    _ ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      exact_mod_cast (show (632623313043 : ℕ) ^ 100 * 2 ^ 66 ≤ 1000000000000 ^ 100 by decide +kernel)

theorem admissible : claimedRadius p q ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [claimedRadius,IRSProfile.minRelativeDistance]

theorem threshold {s:ℕ} (h:(262144:ℝ)*(1-((claimedRadius p q:ℝ≥0):ℝ))≤s) : agreement≤s := by
  have strict:(179768:ℝ)<262144*(1-((claimedRadius p q:ℝ≥0):ℝ)) := by norm_num [claimedRadius]
  exact (show 179768<s by exact_mod_cast strict.trans_le h)

theorem field_budget : (scalarCap+listCap)*2^128≤(0x7f000001:ℕ)^6 := by decide +kernel
theorem reduced : Nat.Coprime p q := by decide +kernel
#print axioms score
#print axioms threshold
end Research6966.ProtocolProfile
