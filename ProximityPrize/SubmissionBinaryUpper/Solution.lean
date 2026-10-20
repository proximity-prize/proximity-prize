/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.PolePencil

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Binary.Upper

-- The exact spot-check comparison at `delta* = 917504/2097152 = 7/16`, in `Nat`:
-- `2 ^ 258175 <= 1179648 ^ 12800` is
-- `2 ^ (-10625/100) <= (1179648/2097152) ^ 128`
-- after clearing denominators (`2097152 = 2^21`) and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 258175 ≤ 1179648 ^ 12800 := by decide

theorem claimedUnsafeRadius_917504_eq :
    claimedUnsafeRadius 917504 = (917504 / 2097152 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [BinaryIRSProfile.Index]

theorem score_base :
    ((2 : ℝ≥0) ^ (10625 : ℕ))⁻¹ ≤ ((1179648 : ℝ≥0) / 2097152) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 268800 ≤ 2 ^ 10625 * 1179648 ^ 12800 := by
    calc (2 : ℕ) ^ 268800 = 2 ^ 10625 * 2 ^ 258175 := by rw [← pow_add]
      _ ≤ 2 ^ 10625 * 1179648 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((2097152 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (268800 : ℕ) := by
    rw [show (2097152 : ℝ≥0) = 2 ^ (21 : ℕ) by norm_num, ← pow_mul]
  have hR : ((2097152 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (1179648 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (10625 : ℕ) := by
    rw [h1]
    have : ((2 : ℕ) ^ 268800 : ℝ≥0) ≤ ((2 ^ 10625 * 1179648 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at this
    calc (2 : ℝ≥0) ^ (268800 : ℕ) ≤ 2 ^ (10625 : ℕ) * 1179648 ^ (12800 : ℕ) := this
      _ = (1179648 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (10625 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((10625 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 917504) ^ BinaryIRSProfile.repetitions := by
  rw [claimedUnsafeRadius_917504_eq]
  have hcross : (1 : ℝ≥0) - 917504 / 2097152 = 1179648 / 2097152 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show BinaryIRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((10625 : ℕ) : ℝ)))
      ≤ ((1179648 : ℝ≥0) / 2097152) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((10625 : ℕ) : ℝ))) * (1 / 100) = -(((10625 : Nat) : ℝ) / 100) by
    push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

/-- The flat-union pole pair certifies `[917504, 1048576)` on the `2^21` grid and
the base-field prescribed-top family the rest of the suffix, giving a
`106.25`-bit upper certificate. -/
theorem candidate : ProtocolClaimUpper 10625 917504 where
  admissible := by
    rw [claimedUnsafeRadius_917504_eq]
    unfold BinaryIRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (917504 / 2097152 : ℝ≥0)
        BinaryIRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_917504_eq] using hδ
    by_cases hmid : δ < (1048576 / 2097152 : ℝ≥0)
    · exact ProximityPrize.SubmissionBinaryUpper.PolePencil.winningSetDensity_gt_epsilon
        δ hband.1 hmid
    · exact ProximityPrize.SubmissionBinaryUpper.PrescribedTop.winningSetDensity_gt_epsilon
        δ (le_trans (div_le_div_of_nonneg_right (by norm_num) (by norm_num) :
          (1015833 / 2097152 : ℝ≥0) ≤ 1048576 / 2097152) (le_of_not_gt hmid)) hband.2
  score := candidate_score

end ProximityPrize.Benchmark.Binary.Upper
