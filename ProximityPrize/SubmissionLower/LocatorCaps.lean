import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 16688064 131071 130000 28 92 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 32831952 131071 5968 56 181 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20134512 131071 10381 33 111 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 92 130000 28 <
    coefficientCount 16688064 131071 130000 28:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateTCap:Fintype.card I * localRankBound 181 5968 56 <
    coefficientCount 32831952 131071 5968 56:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 111 10381 33 <
    coefficientCount 20134512 131071 10381 33:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem full_divisor_mem_box (D w L s m:ℕ)
    (gate:Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1:I → K) (F:P4)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1) :
    F ∈ globalCoefficientBox K D w L s:=by
  classical
  obtain ⟨a,ha,hk⟩:=exists_nonzero_kernel_array (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a ≠ 0:=reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)
theorem full_A_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    F ∈ globalCoefficientBox K 16688064 131071 130000 28:=
  full_divisor_mem_box 16688064 131071 130000 28 92 gateA u0 u1 F hdiv
theorem full_TCap_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 32831952 131071 5968 56 v.1) :
    F ∈ globalCoefficientBox K 32831952 131071 5968 56:=
  full_divisor_mem_box 32831952 131071 5968 56 181 gateTCap u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    F ∈ globalCoefficientBox K 20134512 131071 10381 33:=
  full_divisor_mem_box 20134512 131071 10381 33 111 gateB u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    wt residualYSWeights F ≤ 127:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    16688064 131071 130000 28 (by decide)).mp hbox
  have hr:wt residualSWeights F ≤ 28:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:wt (contactWeights 131071) F ≤ 16688064:=by omega
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 16688064 131071 130000 28 v.1) :
    wt residualSWeights F ≤ 28:=
  ((mem_flagGlobalCoefficientBox_iff F 16688064 131071 130000 28 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    wt residualSWeights F ≤ 33:=
  ((mem_flagGlobalCoefficientBox_iff F 20134512 131071 10381 33 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20134512 131071 10381 33 v.1) :
    wt residualYSWeights F ≤ 153:=by
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    20134512 131071 10381 33 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr:wt residualSWeights F ≤ 33:=hcaps.2.1
  have hc:wt (contactWeights 131071) F ≤ 20134512 - 1:=hcaps.2.2
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  omega
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 32831952 131071 5968 56 v.1) :
    wt residualTotalWeights F ≤ 5964:=by
  by_contra hnot
  have ht:5965 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        32831952 131071 5968 56 181 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          32831952 131071 5968 56 181 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 32831952 131071 3 56:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      32831952 131071 5968 56 181 0 5965 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 5968 - 5965=3 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    32831952 131071 5968 56 181 32831952 3 56
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelTCap_total_quotient_lt
end
end LocatorCaps
