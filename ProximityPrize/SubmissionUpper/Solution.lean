/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_131064_eq_16383_div_32768 :
    claimedUnsafeRadius 131064 = (16383 / 32768 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12799 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 131064) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_131064_eq_16383_div_32768]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 16383 / 32768 = 16385 / 32768 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((12799 : Nat) : ℝ) / 100) =
      (0.01 : ℝ) + (-(128 : ℝ)) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show (16385 : ℝ) / 32768 = (16385 / 16384) * (1 / 2) by ring]
  rw [mul_pow]
  rw [show ((1 : ℝ) / 2) ^ 128 = 2 ^ (-(128 : ℝ)) by
    rw [Real.rpow_neg (by norm_num),
      show (128 : ℝ) = ((128 : Nat) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hbern : (129 : ℝ) / 128 ≤ (16385 / 16384 : ℝ) ^ 128 := by
    have h := one_add_mul_le_pow (a := (1 / 16384 : ℝ)) (by norm_num) 128
    norm_num at h ⊢
  have h2pos : (2 : ℝ) ^ (0.01 : ℝ) ≤ 129 / 128 := by
    apply le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (0.01 : ℝ)) 100]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  linarith [hbern, h2pos]

/-- A coefficient-fiber collision below half radius gives a `127.99`-bit bound. -/
theorem candidate : ProtocolClaimUpper 12799 131064 where
  admissible := by
    rw [claimedUnsafeRadius_131064_eq_16383_div_32768]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (claimedUnsafeRadius 131064)
        IRSProfile.minRelativeDistance := hδ
    rw [ProximityPrize.SubmissionUpper.SubHalfPigeonhole.IRSProfile.winningSetSoundness_eq_one
      δ hband]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
