import ProximityPrize.SubmissionLower.LocatorDivisorBox6803
import ProximityPrize.SubmissionLower.LocatorTCapGate6803

/-! The isolated TCap full-divisor box. -/

namespace ProximityPrize.SubmissionLower.LocatorTCapBox6803

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156
  RCN130

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev TCapKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 32826703 131071 6679 56 181
    IRSProfile.domain u0 u1

theorem full_TCap_divisor_mem_box
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field) (_hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := IRSProfile.Field)
      32826703 131071 6679 56 181 IRSProfile.domain u0 u1,
      F ∣ reconstruct IRSProfile.Field 32826703 131071 6679 56 v.1) :
    F ∈ globalCoefficientBox IRSProfile.Field
      32826703 131071 6679 56 := by
  apply LocatorDivisorBox6803.full_divisor_mem_box
    32826703 131071 6679 56 181 LocatorTCapGate6803.gateTCap
      u0 u1 F
  intro v
  exact hdiv v

end

end ProximityPrize.SubmissionLower.LocatorTCapBox6803
