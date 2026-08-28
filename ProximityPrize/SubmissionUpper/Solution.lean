/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

-- The exact spot-check comparison at `delta* = 122369/262144`, in `Nat`:
-- `2 ^ 218788 <= 139775 ^ 12800` is
-- `2 ^ (-11612/100) <= (139775/262144) ^ 128`
-- after clearing denominators and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := by decide

theorem claimedUnsafeRadius_122369_eq :
    claimedUnsafeRadius 122369 = (122369 / 262144 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem score_base :
    ((2 : ℝ≥0) ^ (11612 : ℕ))⁻¹ ≤ ((139775 : ℝ≥0) / 262144) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 230400 ≤ 2 ^ 11612 * 139775 ^ 12800 := by
    calc (2 : ℕ) ^ 230400 = 2 ^ 11612 * 2 ^ 218788 := by rw [← pow_add]
      _ ≤ 2 ^ 11612 * 139775 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((262144 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (230400 : ℕ) := by
    rw [show (262144 : ℝ≥0) = 2 ^ (18 : ℕ) by norm_num, ← pow_mul]
  have hR : ((262144 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (139775 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11612 : ℕ) := by
    rw [h1]
    have : ((2 : ℕ) ^ 230400 : ℝ≥0) ≤ ((2 ^ 11612 * 139775 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at this
    calc (2 : ℝ≥0) ^ (230400 : ℕ) ≤ 2 ^ (11612 : ℕ) * 139775 ^ (12800 : ℕ) := this
      _ = (139775 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (11612 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((11612 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 122369) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_122369_eq]
  have hcross : (1 : ℝ≥0) - 122369 / 262144 = 139775 / 262144 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show IRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((11612 : ℕ) : ℝ)))
      ≤ ((139775 : ℝ≥0) / 262144) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((11612 : ℕ) : ℝ))) * (1 / 100) = -(((11612 : Nat) : ℝ) / 100) by
    push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

/-- The 512-fibre rational pencil certifies the new narrow window, then hands
off to the prescribed-top attack, giving a `116.12`-bit upper certificate. -/
theorem candidate : ProtocolClaimUpper 11612 122369 where
  admissible := by
    rw [claimedUnsafeRadius_122369_eq]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (122369 / 262144 : ℝ≥0) IRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_122369_eq] using hδ
    by_cases hmid : δ < (122641 / 262144 : ℝ≥0)
    · exact ProximityPrize.SubmissionUpper.OrbitPencil.winningSetDensity_gt_epsilon_window
        δ hband.1 hmid
    · exact ProximityPrize.SubmissionUpper.PrescribedTop.winningSetDensity_gt_epsilon
        δ (le_of_not_gt hmid) hband.2
  score := candidate_score

end ProximityPrize.Benchmark.Upper
