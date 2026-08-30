import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.TwoKernelCaps

namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 12736010 131071 100000 20 70 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 11462409 131071 100000 18 63 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 8187435 131071 43759 13 45 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 15829041 131071 1497 27 87 IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 70 100000 20 <
    coefficientCount 12736010 131071 100000 20 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelA_nullity
  omega
theorem gateAux : Fintype.card I * localRankBound 63 100000 18 <
    coefficientCount 11462409 131071 100000 18 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelAux_nullity
  omega
theorem gateC : Fintype.card I * localRankBound 45 43759 13 <
    coefficientCount 8187435 131071 43759 13 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelC_nullity
  omega
theorem gateB : Fintype.card I * localRankBound 87 1497 27 <
    coefficientCount 15829041 131071 1497 27 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelB_nullity
  omega

theorem full_divisor_mem_box (D w L s m : ℕ)
    (gate : Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1 : I → K) (H : P4)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1,
      H ∣ reconstruct K D w L s v.1) :
    H ∈ globalCoefficientBox K D w L s := by
  classical
  have hExists := exists_nonzero_kernel_array (I := I)
    K D w L s m IRSProfile.domain u0 u1 gate
  obtain ⟨a, ha, hk⟩ := hExists
  let v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1 :=
    ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct K D w L s a ≠ 0 := reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd H (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)

theorem full_A_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, H ∣ reconstruct K 12736010 131071 100000 20 v.1) :
    H ∈ globalCoefficientBox K 12736010 131071 100000 20 :=
  full_divisor_mem_box 12736010 131071 100000 20 70 gateA u0 u1 H hdiv

theorem full_Aux_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : AuxKernel u0 u1, H ∣ reconstruct K 11462409 131071 100000 18 v.1) :
    H ∈ globalCoefficientBox K 11462409 131071 100000 18 :=
  full_divisor_mem_box 11462409 131071 100000 18 63 gateAux u0 u1 H hdiv

theorem full_C_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : CKernel u0 u1, H ∣ reconstruct K 8187435 131071 43759 13 v.1) :
    H ∈ globalCoefficientBox K 8187435 131071 43759 13 :=
  full_divisor_mem_box 8187435 131071 43759 13 45 gateC u0 u1 H hdiv

theorem full_B_divisor_mem_box (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, H ∣ reconstruct K 15829041 131071 1497 27 v.1) :
    H ∈ globalCoefficientBox K 15829041 131071 1497 27 :=
  full_divisor_mem_box 15829041 131071 1497 27 87 gateB u0 u1 H hdiv

theorem common_C_ys_le (u0 u1 : I → K) (H : P4) (_hH : H ≠ 0)
    (hbox : H ∈ globalCoefficientBox K 8187435 131071 43759 13)
    (_hdiv : ∀ v : CKernel u0 u1, H ∣ reconstruct K 8187435 131071 43759 13 v.1) :
    wt residualYSWeights H ≤ 62 := by
  by_contra hnot
  have hy : 63 ≤ wt residualYSWeights H := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H
    8187435 131071 43759 13 (by decide)).mp hbox
  have hr : wt residualSWeights H ≤ 13 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope H 131071 (by decide)
  omega

theorem common_B_total_le (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, H ∣ reconstruct K 15829041 131071 1497 27 v.1) :
    wt residualTotalWeights H ≤ 1497 := by
  have hbox := full_B_divisor_mem_box u0 u1 H hH hdiv
  exact ((mem_flagGlobalCoefficientBox_iff H
    15829041 131071 1497 27 (by decide)).mp hbox).1

end
end ProximityPrize.SubmissionLower.LocatorCaps
