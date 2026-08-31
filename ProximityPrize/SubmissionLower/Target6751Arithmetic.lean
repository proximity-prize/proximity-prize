/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetLower

open ToyProblem
open scoped NNReal

namespace ProximityPrize.SubmissionLower.Target6751Arithmetic

open ProximityPrize.Benchmark

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000000
set_option exponentiation.threshold 300000

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat_6751_at_321083 :
    (727493 : Nat) ^ 12800 * 2 ^ 6751 <= 2 ^ 256000 := by
  decide

theorem radius_321083_complement :
    (1 : NNReal) - claimedRadius 321083 1048576 =
      (727493 : NNReal) / 1048576 := by
  unfold claimedRadius
  rw [tsub_eq_of_eq_add]
  norm_num

theorem score_base_6751_at_321083 :
    ((727493 : NNReal) / 1048576) ^ (12800 : Nat) <=
      ((2 : NNReal) ^ (6751 : Nat))⁻¹ := by
  have hnat := score_nat_6751_at_321083
  have hnnreal :
      (727493 : NNReal) ^ (12800 : Nat) *
          (2 : NNReal) ^ (6751 : Nat) <=
        (1048576 : NNReal) ^ (12800 : Nat) := by
    exact_mod_cast hnat
  rw [div_pow, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [one_mul] using hnnreal

/-- Exact score endpoint for a lower certificate whose safe radius is the top
of the `80270`-error dyadic cell. -/
theorem radius_321083_score_6751 :
    (1 - claimedRadius 321083 1048576) ^ IRSProfile.repetitions <=
      claimedError 6751 := by
  rw [radius_321083_complement]
  have hstart :
      ((727493 : NNReal) / 1048576) ^ ((12800 : Nat) : Real) <=
        (2 : NNReal) ^ (-((6751 : Nat) : Real)) := by
    rw [NNReal.rpow_natCast, NNReal.rpow_neg, NNReal.rpow_natCast]
    exact score_base_6751_at_321083
  have hmono := NNReal.rpow_le_rpow hstart
    (by norm_num : (0 : Real) <= 1 / 100)
  rw [<- NNReal.rpow_mul, <- NNReal.rpow_mul] at hmono
  rw [show ((12800 : Nat) : Real) * (1 / 100) =
      ((128 : Nat) : Real) by norm_num] at hmono
  rw [show (-((6751 : Nat) : Real)) * (1 / 100) =
      -(((6751 : Nat) : Real) / 100) by ring] at hmono
  unfold claimedError
  rw [show IRSProfile.repetitions = 128 from rfl]
  rwa [NNReal.rpow_natCast] at hmono

end ProximityPrize.SubmissionLower.Target6751Arithmetic
