import ProximityPrize.SubmissionLower.PackedLegacyCore2

/-! Generic interpolation-kernel divisor box, isolated for small elaboration. -/

namespace ProximityPrize.SubmissionLower.LocatorDivisorBox6803

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

theorem full_divisor_mem_box (D w L s m : ℕ)
    (gate : Fintype.card IRSProfile.Index * localRankBound m L s <
      coefficientCount D w L s)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (F : MvPolynomial (Fin 4) IRSProfile.Field)
    (hdiv : ∀ v : ConstraintKernel (K := IRSProfile.Field) D w L s m
      IRSProfile.domain u0 u1,
      F ∣ reconstruct IRSProfile.Field D w L s v.1) :
    F ∈ globalCoefficientBox IRSProfile.Field D w L s := by
  classical
  obtain ⟨a, ha, hk⟩ := exists_nonzero_kernel_array (I := I)
    IRSProfile.Field D w L s m IRSProfile.domain u0 u1 gate
  let v : ConstraintKernel (K := IRSProfile.Field) D w L s m
      IRSProfile.domain u0 u1 :=
    ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct IRSProfile.Field D w L s a ≠ 0 :=
    reconstruct_ne_zero IRSProfile.Field D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F
    (reconstruct IRSProfile.Field D w L s a)
    D w L s hQ (hdiv v)
      (reconstruct_mem_globalCoefficientBox IRSProfile.Field D w L s a)

end

end ProximityPrize.SubmissionLower.LocatorDivisorBox6803
