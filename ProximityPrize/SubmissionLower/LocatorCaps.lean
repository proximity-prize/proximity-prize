import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.TwoKernelCaps

namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

abbrev AKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 21834360 131071 138160 37 120 IRSProfile.domain u0 u1
abbrev R10Kernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 13828428 131071 47996 22 76 IRSProfile.domain u0 u1
abbrev R11Kernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 13828428 131071 138160 22 76 IRSProfile.domain u0 u1
abbrev R1213Kernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 14192334 131071 94998 22 78 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 8187885 131071 24496 13 45 IRSProfile.domain u0 u1
abbrev TotalKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 21834360 131071 2505 37 120 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 15829911 131071 1470 27 87 IRSProfile.domain u0 u1

theorem gateA:Fintype.card I*localRankBound 120 138160 37<
    coefficientCount 21834360 131071 138160 37:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateC:Fintype.card I*localRankBound 45 24496 13<
    coefficientCount 8187885 131071 24496 13:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelC_nullity
  omega
theorem gateB:Fintype.card I*localRankBound 87 1470 27<
    coefficientCount 15829911 131071 1470 27:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega

theorem full_divisor_mem_box (D w L s m:ℕ)
    (gate:Fintype.card I*localRankBound m L s<coefficientCount D w L s)
    (u0 u1:I → K) (H:P4)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1,
      H∣reconstruct K D w L s v.1):
    H∈globalCoefficientBox K D w L s:=by
  classical
  have hExists:=exists_nonzero_kernel_array (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  obtain ⟨a,ha,hk⟩:=hExists
  let v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a≠0:=reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd H (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)

theorem full_C_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:CKernel u0 u1,H∣reconstruct K 8187885 131071 24496 13 v.1):
    H∈globalCoefficientBox K 8187885 131071 24496 13:=
  full_divisor_mem_box 8187885 131071 24496 13 45 gateC u0 u1 H hdiv

theorem common_C_ys_le (u0 u1:I → K) (H:P4) (hH:H≠0)
    (hbox:H∈globalCoefficientBox K 8187885 131071 24496 13)
    (hdiv:∀ v:CKernel u0 u1,H∣reconstruct K 8187885 131071 24496 13 v.1):
    wt residualYSWeights H≤60:=by
  by_contra hnot
  have hy:61≤wt residualYSWeights H:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff H
    8187885 131071 24496 13 (by decide)).mp hbox
  have hr:wt residualSWeights H≤13:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope H 131071 (by decide)
  have hc:7995318≤wt (contactWeights 131071) H:=by omega
  have ht:61≤wt residualTotalWeights H:=
    hy.trans (residual_weight_nested H).2
  have hdivK:∀ v:CKernel u0 u1,
      H∣kernelReconstructLinear (K:=K)
        8187885 131071 24496 13 45 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:CKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          8187885 131071 24496 13 45 IRSProfile.domain u0 u1)
        H hdivK v∈globalCoefficientBox K 192567 131071 24435 13:=by
    have h:=TwoKernelCaps.quotient_box_of_full_divisor (K:=K) (I:=I)
      8187885 131071 24496 13 45 7995318 61 0
      IRSProfile.domain u0 u1 H hH hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 8187885 - 7995318=192567 by decide,
      show 24496 - 61=24435 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    8187885 131071 24496 13 45 192567 24435 13
    IRSProfile.domain u0 u1 H hH hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  rw [LocatorArithmetic.C_ys61_quotient_upper] at hobs
  have hnull:=LocatorArithmetic.kernelC_nullity
  omega

theorem common_B_total_le (u0 u1:I → K) (H:P4) (hH:H≠0)
    (hdiv:∀ v:BKernel u0 u1,H∣reconstruct K 15829911 131071 1470 27 v.1):
    wt residualTotalWeights H≤1469:=by
  by_contra hnot
  have ht:1470≤wt residualTotalWeights H:=by omega
  have hdivK:∀ v:BKernel u0 u1,
      H∣kernelReconstructLinear (K:=K)
        15829911 131071 1470 27 87 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          15829911 131071 1470 27 87 IRSProfile.domain u0 u1)
        H hdivK v∈globalCoefficientBox K 15829911 131071 0 27:=by
    have h:=TwoKernelCaps.quotient_box_of_full_divisor (K:=K) (I:=I)
      15829911 131071 1470 27 87 0 1470 0
      IRSProfile.domain u0 u1 H hH hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 1470 - 1470=0 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    15829911 131071 1470 27 87 15829911 0 27
    IRSProfile.domain u0 u1 H hH hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt

end
end ProximityPrize.SubmissionLower.LocatorCaps
