/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionBinaryUpper.PrescribedTop

open ToyProblem
open scoped NNReal

namespace ProximityPrize.Benchmark.Binary.Upper

-- The exact spot-check comparison at `delta* = 1015833/2097152`, in `Nat`:
-- `2 ^ 256567 <= 1081319 ^ 12800` is
-- `2 ^ (-12233/100) <= (1081319/2097152) ^ 128`
-- after clearing denominators (`2097152 = 2^21`) and raising to the hundredth power.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat : (2 : ℕ) ^ 256567 ≤ 1081319 ^ 12800 := by decide

theorem claimedUnsafeRadius_1015833_eq :
    claimedUnsafeRadius 1015833 = (1015833 / 2097152 : ℝ≥0) := by
  unfold claimedUnsafeRadius ProximityGap.gridPt
  norm_num [BinaryIRSProfile.Index]

theorem score_base :
    ((2 : ℝ≥0) ^ (12233 : ℕ))⁻¹ ≤ ((1081319 : ℝ≥0) / 2097152) ^ (12800 : ℕ) := by
  have hnat : (2 : ℕ) ^ 268800 ≤ 2 ^ 12233 * 1081319 ^ 12800 := by
    calc (2 : ℕ) ^ 268800 = 2 ^ 12233 * 2 ^ 256567 := by rw [← pow_add]
      _ ≤ 2 ^ 12233 * 1081319 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have h1 : ((2097152 : ℝ≥0)) ^ (12800 : ℕ) = (2 : ℝ≥0) ^ (268800 : ℕ) := by
    rw [show (2097152 : ℝ≥0) = 2 ^ (21 : ℕ) by norm_num, ← pow_mul]
  have hR : ((2097152 : ℝ≥0)) ^ (12800 : ℕ)
      ≤ (1081319 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (12233 : ℕ) := by
    rw [h1]
    have : ((2 : ℕ) ^ 268800 : ℝ≥0) ≤ ((2 ^ 12233 * 1081319 ^ 12800 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    push_cast at this
    calc (2 : ℝ≥0) ^ (268800 : ℕ) ≤ 2 ^ (12233 : ℕ) * 1081319 ^ (12800 : ℕ) := this
      _ = (1081319 : ℝ≥0) ^ (12800 : ℕ) * (2 : ℝ≥0) ^ (12233 : ℕ) := by ring
  rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (by positivity)]
  exact hR

theorem candidate_score :
    (2 : ℝ≥0) ^ (-(((12233 : Nat) : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius 1015833) ^ BinaryIRSProfile.repetitions := by
  rw [claimedUnsafeRadius_1015833_eq]
  have hcross : (1 : ℝ≥0) - 1015833 / 2097152 = 1081319 / 2097152 := by
    rw [tsub_eq_of_eq_add]
    norm_num
  rw [show BinaryIRSProfile.repetitions = 128 from rfl, hcross]
  have hstart : (2 : ℝ≥0) ^ (-(((12233 : ℕ) : ℝ)))
      ≤ ((1081319 : ℝ≥0) / 2097152) ^ ((12800 : ℕ) : ℝ) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact score_base
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : ℝ) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(((12233 : ℕ) : ℝ))) * (1 / 100) = -(((12233 : Nat) : ℝ) / 100) by
    push_cast; ring] at hmono
  rw [show ((12800 : ℕ) : ℝ) * (1 / 100) = ((128 : ℕ) : ℝ) by push_cast; norm_num] at hmono
  rwa [NNReal.rpow_natCast] at hmono

/-- Prescribing the top `32743` coefficients of the vanishing polynomial of a
`1081319`-subset leaves a fibre of more than `2^64` subsets, giving a
`122.33`-bit upper certificate. -/
theorem candidate : ProtocolClaimUpper 12233 1015833 where
  admissible := by
    rw [claimedUnsafeRadius_1015833_eq]
    unfold BinaryIRSProfile.minRelativeDistance
    norm_num
  unsafeAbove := by
    intro δ hδ
    have hband : δ ∈ Set.Ico (1015833 / 2097152 : ℝ≥0)
        BinaryIRSProfile.minRelativeDistance := by
      simpa only [claimedUnsafeRadius_1015833_eq] using hδ
    exact ProximityPrize.SubmissionBinaryUpper.PrescribedTop.winningSetDensity_gt_epsilon
      δ hband.1 hband.2
  score := candidate_score

end ProximityPrize.Benchmark.Binary.Upper
