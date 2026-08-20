/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.IRSHalfRadius

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Upper

theorem claimedUnsafeRadius_131072_eq_half :
    claimedUnsafeRadius 131072 = (1 / 2 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [IRSProfile.Index]

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12800 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 131072) ^ IRSProfile.repetitions := by
  rw [claimedUnsafeRadius_131072_eq_half]
  have ht : IRSProfile.repetitions = 128 := rfl
  have hcross : (1 : ℝ≥0) - 1 / 2 = 1 / 2 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [ht, hcross]
  have hbits : -(((12800 : Nat) : ℝ) / 100) = -(128 : ℝ) := by
    norm_num
  rw [hbits, ← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (128 : ℝ) = ((128 : Nat) : ℝ) by norm_num,
    Real.rpow_natCast, div_pow, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  norm_num

/-- The half-radius interpolation attack gives a `128.00`-bit attack-point seed. -/
theorem candidate : ProtocolClaimUpper 12800 131072 where
  admissible := by
    rw [claimedUnsafeRadius_131072_eq_half]
    unfold IRSProfile.minRelativeDistance
    norm_num
  unsafeAt := by
    have hband : (1 / 2 : ℝ≥0) ∈
        Set.Ico (1 / 2 : ℝ≥0) IRSProfile.minRelativeDistance := by
      constructor
      · rfl
      · unfold IRSProfile.minRelativeDistance
        norm_num
    rw [claimedUnsafeRadius_131072_eq_half]
    rw [ProximityPrize.SubmissionUpper.IRSHalfRadius.IRSProfile.winningSetSoundness_eq_one
      (1 / 2 : ℝ≥0) hband]
    unfold epsilonStar ProximityGap.prizeThreshold
    norm_num
  score := candidate_score

end ProximityPrize.Benchmark.Upper
