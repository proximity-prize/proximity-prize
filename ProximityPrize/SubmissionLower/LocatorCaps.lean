import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorSourceArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient

/-! Whole-kernel divisor caps for the 67.54 joined Y50/R50/B97 sources. -/
namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
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
  ConstraintKernel (K := K) 9092250 131071 100000 14 50 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 9092250 131071 100000 15 50 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 16184205 131071 109000 27 89 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 17638965 131071 1799 30 97 IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 50 100000 14 <
    coefficientCount 9092250 131071 100000 14 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorSourceArithmetic.R_nullity
  omega

theorem gateAux : Fintype.card I * localRankBound 50 100000 15 <
    coefficientCount 9092250 131071 100000 15 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorSourceArithmetic.Y_nullity
  omega

theorem gateC : Fintype.card I * localRankBound 89 109000 27 <
    coefficientCount 16184205 131071 109000 27 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorSourceArithmetic.ambient_nullity
  omega

theorem gateB : Fintype.card I * localRankBound 97 1799 30 <
    coefficientCount 17638965 131071 1799 30 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorSourceArithmetic.B_nullity
  omega

theorem full_divisor_mem_box (D w L s m : ℕ)
    (gate : Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1 : I → K) (F : P4)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1) :
    F ∈ globalCoefficientBox K D w L s := by
  classical
  obtain ⟨a, ha, hk⟩ := exists_nonzero_kernel_array (I := I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1 :=
    ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct K D w L s a ≠ 0 := reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)

theorem full_A_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 9092250 131071 100000 14 v.1) :
    F ∈ globalCoefficientBox K 9092250 131071 100000 14 :=
  full_divisor_mem_box 9092250 131071 100000 14 50 gateA u0 u1 F hdiv

theorem full_Aux_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : AuxKernel u0 u1, F ∣ reconstruct K 9092250 131071 100000 15 v.1) :
    F ∈ globalCoefficientBox K 9092250 131071 100000 15 :=
  full_divisor_mem_box 9092250 131071 100000 15 50 gateAux u0 u1 F hdiv

theorem full_C_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : CKernel u0 u1, F ∣ reconstruct K 16184205 131071 109000 27 v.1) :
    F ∈ globalCoefficientBox K 16184205 131071 109000 27 :=
  full_divisor_mem_box 16184205 131071 109000 27 89 gateC u0 u1 F hdiv

theorem full_B_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, F ∣ reconstruct K 17638965 131071 1799 30 v.1) :
    F ∈ globalCoefficientBox K 17638965 131071 1799 30 :=
  full_divisor_mem_box 17638965 131071 1799 30 97 gateB u0 u1 F hdiv

theorem common_Aux_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AuxKernel u0 u1, F ∣ reconstruct K 9092250 131071 100000 15 v.1) :
    wt residualYSWeights F ≤ 66 := by
  have hbox := full_Aux_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy : 67 ≤ wt residualYSWeights F := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    9092250 131071 100000 15 (by decide)).mp hbox
  let r := wt residualSWeights F
  have hr : r ≤ 15 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 67 * 131071 - r ≤ wt (contactWeights 131071) F := by
    dsimp only [r]
    omega
  have ht : 67 ≤ wt residualTotalWeights F :=
    hy.trans (residual_weight_nested F).2
  have hdivK : ∀ v : AuxKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        9092250 131071 100000 15 50 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : AuxKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          9092250 131071 100000 15 50 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K
          (9092250 - (67 * 131071 - r)) 131071 99933 (15 - r) := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor (K := K) (I := I)
      9092250 131071 100000 15 50 (67 * 131071 - r) 67 r
      IRSProfile.domain u0 u1 F hF hdivK hc ht (le_refl r)
    intro v
    simpa only [show 100000 - 67 = 99933 by decide] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    9092250 131071 100000 15 50
      (9092250 - (67 * 131071 - r)) 99933 (15 - r)
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) (LocatorSourceArithmetic.Y_ys67_quotient_lt r hr)

theorem common_A_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 9092250 131071 100000 14 v.1) :
    wt residualSWeights F ≤ 14 :=
  ((mem_flagGlobalCoefficientBox_iff F 9092250 131071 100000 14 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1

theorem common_A_contact_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 9092250 131071 100000 14 v.1) :
    wt (contactWeights 131071) F ≤ 9092249 :=
  ((mem_flagGlobalCoefficientBox_iff F 9092250 131071 100000 14 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.2

theorem common_B_total_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, F ∣ reconstruct K 17638965 131071 1799 30 v.1) :
    wt residualTotalWeights F ≤ 1796 := by
  by_contra hnot
  have ht : 1797 ≤ wt residualTotalWeights F := by omega
  have hdivK : ∀ v : BKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        17638965 131071 1799 30 97 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          17638965 131071 1799 30 97 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 17638965 131071 2 30 := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor (K := K) (I := I)
      17638965 131071 1799 30 97 0 1797 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero, show 1799 - 1797 = 2 by decide] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    17638965 131071 1799 30 97 17638965 2 30
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorSourceArithmetic.B_total_quotient_lt

end
end ProximityPrize.SubmissionLower.LocatorCaps
