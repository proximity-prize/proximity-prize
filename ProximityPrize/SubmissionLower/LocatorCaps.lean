import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient

/-! Whole-kernel divisor caps for the 67.51 A48/B94 pair.
The auxiliary A61/A68 kernels are independent of any selected interpolants. -/
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
  ConstraintKernel (K := K) 8729952 131071 109000 14 48 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 11094314 131071 10000 18 61 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 12367432 131071 10000 20 68 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 17096156 131071 1702 29 94 IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 48 109000 14 <
    coefficientCount 8729952 131071 109000 14 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelA_nullity
  omega

theorem gateAux : Fintype.card I * localRankBound 61 10000 18 <
    coefficientCount 11094314 131071 10000 18 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelAux_nullity
  omega

theorem gateC : Fintype.card I * localRankBound 68 10000 20 <
    coefficientCount 12367432 131071 10000 20 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelC_nullity
  omega

theorem gateB : Fintype.card I * localRankBound 94 1702 29 <
    coefficientCount 17096156 131071 1702 29 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic.kernelB_nullity
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
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 8729952 131071 109000 14 v.1) :
    F ∈ globalCoefficientBox K 8729952 131071 109000 14 :=
  full_divisor_mem_box 8729952 131071 109000 14 48 gateA u0 u1 F hdiv

theorem full_Aux_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : AuxKernel u0 u1, F ∣ reconstruct K 11094314 131071 10000 18 v.1) :
    F ∈ globalCoefficientBox K 11094314 131071 10000 18 :=
  full_divisor_mem_box 11094314 131071 10000 18 61 gateAux u0 u1 F hdiv

theorem full_C_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : CKernel u0 u1, F ∣ reconstruct K 12367432 131071 10000 20 v.1) :
    F ∈ globalCoefficientBox K 12367432 131071 10000 20 :=
  full_divisor_mem_box 12367432 131071 10000 20 68 gateC u0 u1 F hdiv

theorem full_B_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, F ∣ reconstruct K 17096156 131071 1702 29 v.1) :
    F ∈ globalCoefficientBox K 17096156 131071 1702 29 :=
  full_divisor_mem_box 17096156 131071 1702 29 94 gateB u0 u1 F hdiv

theorem common_A_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 8729952 131071 109000 14 v.1) :
    wt residualYSWeights F ≤ 64 := by
  have hbox := full_A_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy : 65 ≤ wt residualYSWeights F := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    8729952 131071 109000 14 (by decide)).mp hbox
  have hr : wt residualSWeights F ≤ 14 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : 8519601 ≤ wt (contactWeights 131071) F := by omega
  have ht : 65 ≤ wt residualTotalWeights F :=
    hy.trans (residual_weight_nested F).2
  have hdivK : ∀ v : AKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        8729952 131071 109000 14 48 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : AKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          8729952 131071 109000 14 48 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 210351 131071 108935 14 := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor (K := K) (I := I)
      8729952 131071 109000 14 48 8519601 65 0
      IRSProfile.domain u0 u1 F hF hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 8729952 - 8519601 = 210351 by decide,
      show 109000 - 65 = 108935 by decide, Nat.sub_zero] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    8729952 131071 109000 14 48 210351 108935 14
    IRSProfile.domain u0 u1 F hF hdivK hq
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity,
    LocatorArithmetic.A_ys65_quotient_upper] at hobs
  omega

theorem common_A_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 8729952 131071 109000 14 v.1) :
    wt residualSWeights F ≤ 14 :=
  ((mem_flagGlobalCoefficientBox_iff F 8729952 131071 109000 14 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1

theorem common_A_contact_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1, F ∣ reconstruct K 8729952 131071 109000 14 v.1) :
    wt (contactWeights 131071) F ≤ 8729951 :=
  ((mem_flagGlobalCoefficientBox_iff F 8729952 131071 109000 14 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.2

theorem common_B_total_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1, F ∣ reconstruct K 17096156 131071 1702 29 v.1) :
    wt residualTotalWeights F ≤ 1698 := by
  by_contra hnot
  have ht : 1699 ≤ wt residualTotalWeights F := by omega
  have hdivK : ∀ v : BKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        17096156 131071 1702 29 94 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          17096156 131071 1702 29 94 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 17096156 131071 3 29 := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor (K := K) (I := I)
      17096156 131071 1702 29 94 0 1699 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero, show 1702 - 1699 = 3 by decide] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    17096156 131071 1702 29 94 17096156 3 29
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt

end
end ProximityPrize.SubmissionLower.LocatorCaps
