import ProximityPrize.SubmissionLower.BCHKSBridge

/-!
# Exact first target strictly above 64.00 bits

This file records the score-64.01 radius and, importantly, the arithmetic
phase transition in the ordinary full-domain Guruswami--Sudan count.  At
64.00 the agreement count is just above the Johnson square-root threshold;
at 64.01 it is strictly below it.  Consequently any proof at this score must
use additional structure rather than merely retune the full-domain kernel.
-/

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

noncomputable def bchksRadius6401 : ℝ≥0 :=
  (307161 : ℝ≥0) / 1048576

def bchksErrors6401 : ℕ := 76790
def bchksAgreements6401 : ℕ := 185354

lemma bchksRadius6401_floor :
    ⌊(bchksRadius6401 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors6401 := by
  norm_num [bchksRadius6401, bchksErrors6401, IRSProfile.Index]

lemma bchksRadius6401_floor_nnreal :
    ⌊bchksRadius6401 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors6401 := by
  norm_num [bchksRadius6401, bchksErrors6401, IRSProfile.Index]

lemma bchks6401_agreement_identity :
    262144 - bchksErrors6401 = bchksAgreements6401 := by
  norm_num [bchksErrors6401, bchksAgreements6401]

/-- A rational upper approximation to `2^(1/100)`, used in the 64.01 score
check.  The direction is deliberately opposite to the 63.99 certificate. -/
theorem two_rpow_one_hundred_le_12587_div_12500 :
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) ≤ 12587 / 12500 := by
  have hroot :
      ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ 12587 / 12500 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ 12587 / 12500 := hroot

/-- Exact score arithmetic for the first centibit strictly above 64.00. -/
lemma bchksRadius6401_score :
    (1 - bchksRadius6401) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6401 := by
  have hinv :
      (12500 / 12587 : ℝ≥0) ≤ (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
    rw [NNReal.rpow_neg]
    have h := two_rpow_one_hundred_le_12587_div_12500
    have hi := (inv_le_inv₀
      (show (0 : ℝ≥0) < 12587 / 12500 by positivity)
      (show (0 : ℝ≥0) < (2 : ℝ≥0) ^ ((1 : ℝ) / 100) by positivity)).2 h
    norm_num [div_eq_mul_inv] at hi ⊢
    exact hi
  calc
    (1 - bchksRadius6401) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (12500 / 12587) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius6401, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
          (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = ProximityPrize.Benchmark.claimedError 6401 := by
      have h64 : ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) =
          (2 : ℝ≥0) ^ (-((64 : ℕ) : ℝ)) := by
        rw [NNReal.rpow_neg, NNReal.rpow_natCast]
        simp
      rw [h64]
      unfold ProximityPrize.Benchmark.claimedError
      rw [show -((((6401 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + -((1 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]

/-- The full 262144-coordinate Johnson quadratic is already negative at
64.01. -/
lemma bchks6401_fullDomain_below_Johnson :
    bchksAgreements6401 ^ 2 < 262144 * 131071 := by
  norm_num [bchksAgreements6401]

lemma bchks6401_fullDomain_Johnson_deficit :
    262144 * 131071 - bchksAgreements6401 ^ 2 = 3370908 := by
  norm_num [bchksAgreements6401]

/-- `262118` is the largest identity-domain size on which the ordinary
quadratic dimension inequality can still hold at this agreement count. -/
lemma bchks6401_identityDomain_Johnson_endpoint :
    262118 * 131071 < bchksAgreements6401 ^ 2 ∧
      bchksAgreements6401 ^ 2 ≤ 262119 * 131071 := by
  norm_num [bchksAgreements6401]

lemma bchks6401_identityDomain_residual_zero_coords :
    262144 - 262119 = 25 := by
  norm_num

end ProximityPrize.SubmissionLower
