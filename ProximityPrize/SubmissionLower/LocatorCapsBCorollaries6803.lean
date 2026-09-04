import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorCapsBBox6803

/-! The isolated B-profile middle and slope corollaries. -/

namespace ProximityPrize.SubmissionLower.LocatorCapsBCorollaries6803

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN234 RCN156

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open LocatorCapsBBox6803

local instance : DecidableEq K := Classical.decEq K

theorem common_B_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      F ∣ reconstruct K 20131293 131071 14261 34 v.1) :
    wt residualYSWeights F ≤ 153 := by
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    20131293 131071 14261 34 (by decide)).mp
      (full_B_divisor_mem_box u0 u1 F hF hdiv)
  exact LocatorCapArithmetic6803.B_middle_le
    (residualYS_mul_le_contact_add_slope F 131071 (by decide))
    hcaps.2.2 hcaps.2.1

theorem common_B_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      F ∣ reconstruct K 20131293 131071 14261 34 v.1) :
    wt residualSWeights F ≤ 34 :=
  ((mem_flagGlobalCoefficientBox_iff F
    20131293 131071 14261 34 (by decide)).mp
      (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1

end

end ProximityPrize.SubmissionLower.LocatorCapsBCorollaries6803
