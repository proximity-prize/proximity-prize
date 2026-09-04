import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorCapsABox6803

/-! The isolated A-profile middle and slope corollaries. -/

namespace ProximityPrize.SubmissionLower.LocatorCapsACorollaries6803

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN234 RCN156

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open LocatorCapsABox6803

local instance : DecidableEq K := Classical.decEq K

theorem common_A_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 17773574 131071 130000 29 v.1) :
    wt residualYSWeights F ≤ 135 := by
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    17773574 131071 130000 29 (by decide)).mp
      (full_A_divisor_mem_box u0 u1 F hF hdiv)
  exact LocatorCapArithmetic6803.A_middle_le
    (residualYS_mul_le_contact_add_slope F 131071 (by decide))
    hcaps.2.2 hcaps.2.1

theorem common_A_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 17773574 131071 130000 29 v.1) :
    wt residualSWeights F ≤ 29 :=
  ((mem_flagGlobalCoefficientBox_iff F
    17773574 131071 130000 29 (by decide)).mp
      (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1

end

end ProximityPrize.SubmissionLower.LocatorCapsACorollaries6803
