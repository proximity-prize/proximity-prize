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
  ConstraintKernel (K:=K) 11986194 131071 149307 19 66 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 22882734 131071 3066 39 126 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 66 149307 19 <
    coefficientCount 11986194 131071 149307 19:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateTCap:Fintype.card I * localRankBound 126 3066 39 <
    coefficientCount 22882734 131071 3066 39:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
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
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 11986194 131071 149307 19 v.1) :
    F ∈ globalCoefficientBox K 11986194 131071 149307 19:=
  full_divisor_mem_box 11986194 131071 149307 19 66 gateA u0 u1 F hdiv
theorem full_TCap_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 22882734 131071 3066 39 v.1) :
    F ∈ globalCoefficientBox K 22882734 131071 3066 39:=
  full_divisor_mem_box 22882734 131071 3066 39 126 gateTCap u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 11986194 131071 149307 19 v.1) :
    wt residualYSWeights F ≤ 89:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy:90 ≤ wt residualYSWeights F:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    11986194 131071 149307 19 (by decide)).mp hbox
  have hr:wt residualSWeights F ≤ 19:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:11796371 ≤ wt (contactWeights 131071) F:=by omega
  have ht:90 ≤ wt residualTotalWeights F:=
    hy.trans (residual_weight_nested F).2
  have hdivK:∀ v:AKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        11986194 131071 149307 19 66 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:AKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          11986194 131071 149307 19 66 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 189823 131071 149217 19:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      11986194 131071 149307 19 66 11796371 90 0
      IRSProfile.domain u0 u1 F hF hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 11986194 - 11796371=189823 by decide,
      show 149307 - 90=149217 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    11986194 131071 149307 19 66 189823 149217 19
    IRSProfile.domain u0 u1 F hF hdivK hq
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity,
    LocatorArithmetic.A_ys89_quotient_upper] at hobs
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 11986194 131071 149307 19 v.1) :
    wt residualSWeights F ≤ 19:=
  ((mem_flagGlobalCoefficientBox_iff F 11986194 131071 149307 19 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 22882734 131071 3066 39 v.1) :
    wt residualTotalWeights F ≤ 3063:=by
  by_contra hnot
  have ht:3064 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        22882734 131071 3066 39 126 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          22882734 131071 3066 39 126 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 22882734 131071 2 39:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      22882734 131071 3066 39 126 0 3064 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 3066 - 3064=2 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    22882734 131071 3066 39 126 22882734 2 39
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelTCap_total_quotient_lt
end
end LocatorCaps
