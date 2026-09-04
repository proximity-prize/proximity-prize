import ProximityPrize.SubmissionLower.LocatorCapsAGate6803
import ProximityPrize.SubmissionLower.LocatorDivisorBox6803

/-! The isolated A-profile full-divisor box. -/

namespace ProximityPrize.SubmissionLower.LocatorCapsABox6803

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

abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 17773574 131071 130000 29 98
    IRSProfile.domain u0 u1

theorem full_A_divisor_mem_box
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field) (_hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := IRSProfile.Field)
      17773574 131071 130000 29 98 IRSProfile.domain u0 u1,
      F ∣ reconstruct IRSProfile.Field 17773574 131071 130000 29 v.1) :
    F ∈ globalCoefficientBox IRSProfile.Field
      17773574 131071 130000 29 := by
  apply LocatorDivisorBox6803.full_divisor_mem_box
    17773574 131071 130000 29 98 LocatorCapsAGate6803.gateA
      u0 u1 F
  intro v
  exact hdiv v

end

end ProximityPrize.SubmissionLower.LocatorCapsABox6803
