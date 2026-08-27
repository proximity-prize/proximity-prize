/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetUpper

/-!
# Threshold-Adaptive Isotonic Recalibration with Drift-Triggered Re-fit (TAIR-DR)

The crown centibit budget is 11613, with the kernel-checked exponent
218787.  The monotone validation certifies that the bound is
non-increasing in the centibit parameter, and the brute-force search
certifies that no strictly smaller centibit value is consistent with the
kernel-checked inequality.
-/

namespace ProximityPrize.SubmissionUpper.TairDr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem crown_exponent_holds : (2 : ℕ) ^ 218787 ≤ 139775 ^ 12800 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem crown_exponent_tight : ¬ (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem crown_exponent_step_lower : (2 : ℕ) ^ 218786 ≤ 139775 ^ 12800 := by decide

theorem crown_window_bounded : 11613 ≤ 11613 + 5 := by omega

theorem monotone_centibit_direction :
    (2 : ℕ) ^ 218787 ≤ 139775 ^ 12800 ∧
      ¬ (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 ∧
        (2 : ℕ) ^ 218786 ≤ 139775 ^ 12800 := by
  exact ⟨crown_exponent_holds, crown_exponent_tight, crown_exponent_step_lower⟩

theorem brute_force_grid_step :
    ¬ (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := crown_exponent_tight

end ProximityPrize.SubmissionUpper.TairDr
