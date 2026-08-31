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
  ConstraintKernel (K:=K) 10177776 131071 51967 17 56 IRSProfile.domain u0 u1
abbrev ThinKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 10177776 131071 51967 16 56 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 17629362 131071 2241 30 97 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 56 51967 17 <
    coefficientCount 10177776 131071 51967 17:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateThin:Fintype.card I * localRankBound 56 51967 16 <
    coefficientCount 10177776 131071 51967 16:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelThin_nullity
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
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 10177776 131071 51967 17 v.1) :
    F ∈ globalCoefficientBox K 10177776 131071 51967 17:=
  full_divisor_mem_box 10177776 131071 51967 17 56 gateA u0 u1 F hdiv
theorem full_Thin_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:ThinKernel u0 u1,F ∣ reconstruct K 10177776 131071 51967 16 v.1) :
    F ∈ globalCoefficientBox K 10177776 131071 51967 16:=
  full_divisor_mem_box 10177776 131071 51967 16 56 gateThin u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 10177776 131071 51967 17 v.1) :
    wt residualYSWeights F ≤ 74:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy:75 ≤ wt residualYSWeights F:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    10177776 131071 51967 17 (by decide)).mp hbox
  have hr:wt residualSWeights F ≤ 17:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:9830308 ≤ wt (contactWeights 131071) F:=by omega
  have ht:75 ≤ wt residualTotalWeights F:=
    hy.trans (residual_weight_nested F).2
  have hdivK:∀ v:AKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        10177776 131071 51967 17 56 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:AKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          10177776 131071 51967 17 56 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 347468 131071 51892 17:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      10177776 131071 51967 17 56 9830308 75 0
      IRSProfile.domain u0 u1 F hF hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 10177776 - 9830308=347468 by decide,
      show 51967 - 75=51892 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    10177776 131071 51967 17 56 347468 51892 17
    IRSProfile.domain u0 u1 F hF hdivK hq
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity,
    LocatorArithmetic.A_ys75_quotient_upper] at hobs
  omega
theorem common_Thin_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:ThinKernel u0 u1,F ∣ reconstruct K 10177776 131071 51967 16 v.1) :
    wt residualSWeights F ≤ 16:=
  ((mem_flagGlobalCoefficientBox_iff F 10177776 131071 51967 16 (by decide)).mp
    (full_Thin_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 17629362 131071 2241 30 v.1) :
    wt residualTotalWeights F ≤ 2239:=by
  by_contra hnot
  have ht:2240 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:BKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        17629362 131071 2241 30 97 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          17629362 131071 2241 30 97 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 17629362 131071 1 30:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      17629362 131071 2241 30 97 0 2240 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 2241 - 2240=1 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    17629362 131071 2241 30 97 17629362 1 30
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt
end
end LocatorCaps
