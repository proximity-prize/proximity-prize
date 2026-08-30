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
  ConstraintKernel (K:=K) 16193817 131071 100000 27 89 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 13464522 131071 98880 21 74 IRSProfile.domain u0 u1
abbrev Aux23Kernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 14738193 131071 70548 23 81 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 8187885 131071 62248 13 45 IRSProfile.domain u0 u1
abbrev ThinKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 14738193 131071 62316 24 81 IRSProfile.domain u0 u1
abbrev TradeKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 16193817 131071 2748 27 89 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K):=
  ConstraintKernel (K:=K) 15829911 131071 1471 27 87 IRSProfile.domain u0 u1

theorem gateA:Fintype.card I*localRankBound 89 100000 27<
    coefficientCount 16193817 131071 100000 27:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateAux:Fintype.card I*localRankBound 74 98880 21<
    coefficientCount 13464522 131071 98880 21:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelAux_nullity
  omega
theorem gateAux23:Fintype.card I*localRankBound 81 70548 23<
    coefficientCount 14738193 131071 70548 23:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelAux23_nullity
  omega
theorem gateC:Fintype.card I*localRankBound 45 62248 13<
    coefficientCount 8187885 131071 62248 13:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelC_nullity
  omega
theorem gateThin:Fintype.card I*localRankBound 81 62316 24<
    coefficientCount 14738193 131071 62316 24:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelThin_nullity
  omega
theorem gateTrade:Fintype.card I*localRankBound 89 2748 27<
    coefficientCount 16193817 131071 2748 27:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTrade_nullity
  omega
theorem gateB:Fintype.card I*localRankBound 87 1471 27<
    coefficientCount 15829911 131071 1471 27:=by
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

theorem full_A_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:AKernel u0 u1,H∣reconstruct K 16193817 131071 100000 27 v.1):
    H∈globalCoefficientBox K 16193817 131071 100000 27:=
  full_divisor_mem_box 16193817 131071 100000 27 89 gateA u0 u1 H hdiv

theorem full_Aux_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:AuxKernel u0 u1,H∣reconstruct K 13464522 131071 98880 21 v.1):
    H∈globalCoefficientBox K 13464522 131071 98880 21:=
  full_divisor_mem_box 13464522 131071 98880 21 74 gateAux u0 u1 H hdiv

theorem full_Aux23_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:Aux23Kernel u0 u1,H∣reconstruct K 14738193 131071 70548 23 v.1):
    H∈globalCoefficientBox K 14738193 131071 70548 23:=
  full_divisor_mem_box 14738193 131071 70548 23 81 gateAux23 u0 u1 H hdiv

theorem full_C_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:CKernel u0 u1,H∣reconstruct K 8187885 131071 62248 13 v.1):
    H∈globalCoefficientBox K 8187885 131071 62248 13:=
  full_divisor_mem_box 8187885 131071 62248 13 45 gateC u0 u1 H hdiv

theorem full_Thin_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:ThinKernel u0 u1,H∣reconstruct K 14738193 131071 62316 24 v.1):
    H∈globalCoefficientBox K 14738193 131071 62316 24:=
  full_divisor_mem_box 14738193 131071 62316 24 81 gateThin u0 u1 H hdiv

theorem full_Trade_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:TradeKernel u0 u1,H∣reconstruct K 16193817 131071 2748 27 v.1):
    H∈globalCoefficientBox K 16193817 131071 2748 27:=
  full_divisor_mem_box 16193817 131071 2748 27 89 gateTrade u0 u1 H hdiv

theorem full_B_divisor_mem_box (u0 u1:I → K) (H:P4) (_hH:H≠0)
    (hdiv:∀ v:BKernel u0 u1,H∣reconstruct K 15829911 131071 1471 27 v.1):
    H∈globalCoefficientBox K 15829911 131071 1471 27:=
  full_divisor_mem_box 15829911 131071 1471 27 87 gateB u0 u1 H hdiv

theorem common_C_ys_le (u0 u1:I → K) (H:P4) (hH:H≠0)
    (hbox:H∈globalCoefficientBox K 8187885 131071 62248 13)
    (hdiv:∀ v:CKernel u0 u1,H∣reconstruct K 8187885 131071 62248 13 v.1):
    wt residualYSWeights H≤60:=by
  by_contra hnot
  have hy:61≤wt residualYSWeights H:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff H
    8187885 131071 62248 13 (by decide)).mp hbox
  have hr:wt residualSWeights H≤13:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope H 131071 (by decide)
  have hc:7995318≤wt (contactWeights 131071) H:=by omega
  have ht:61≤wt residualTotalWeights H:=
    hy.trans (residual_weight_nested H).2
  have hdivK:∀ v:CKernel u0 u1,
      H∣kernelReconstructLinear (K:=K)
        8187885 131071 62248 13 45 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:CKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          8187885 131071 62248 13 45 IRSProfile.domain u0 u1)
        H hdivK v∈globalCoefficientBox K 192567 131071 62187 13:=by
    have h:=TwoKernelCaps.quotient_box_of_full_divisor (K:=K) (I:=I)
      8187885 131071 62248 13 45 7995318 61 0
      IRSProfile.domain u0 u1 H hH hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 8187885 - 7995318=192567 by decide,
      show 62248 - 61=62187 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    8187885 131071 62248 13 45 192567 62187 13
    IRSProfile.domain u0 u1 H hH hdivK hq
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelC_nullity,
    LocatorArithmetic.C_ys61_quotient_upper] at hobs
  omega

theorem common_B_total_le (u0 u1:I → K) (H:P4) (hH:H≠0)
    (hdiv:∀ v:BKernel u0 u1,H∣reconstruct K 15829911 131071 1471 27 v.1):
    wt residualTotalWeights H≤1468:=by
  by_contra hnot
  have ht:1469≤wt residualTotalWeights H:=by omega
  have hdivK:∀ v:BKernel u0 u1,
      H∣kernelReconstructLinear (K:=K)
        15829911 131071 1471 27 87 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          15829911 131071 1471 27 87 IRSProfile.domain u0 u1)
        H hdivK v∈globalCoefficientBox K 15829911 131071 2 27:=by
    have h:=TwoKernelCaps.quotient_box_of_full_divisor (K:=K) (I:=I)
      15829911 131071 1471 27 87 0 1469 0
      IRSProfile.domain u0 u1 H hH hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 1471 - 1469=2 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    15829911 131071 1471 27 87 15829911 2 27
    IRSProfile.domain u0 u1 H hH hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt

end
end ProximityPrize.SubmissionLower.LocatorCaps
