import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I→ K):=
  ConstraintKernel (K:=K) 9996580 131071 79970 16 55 IRSProfile.domain u0 u1
abbrev AuxKernel (u0 u1:I→ K):=
  ConstraintKernel (K:=K) 13086432 131071 79970 21 72 IRSProfile.domain u0 u1
abbrev CKernel (u0 u1:I→ K):=
  ConstraintKernel (K:=K) 22901256 131071 79970 39 126 IRSProfile.domain u0 u1
abbrev ThinKernel (u0 u1:I→ K):=
  ConstraintKernel (K:=K) 17266820 131071 79970 29 95 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I→ K):=
  ConstraintKernel (K:=K) 17630332 131071 2187 30 97 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 55 79970 16<
    coefficientCount 9996580 131071 79970 16:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateAux:Fintype.card I * localRankBound 72 79970 21<
    coefficientCount 13086432 131071 79970 21:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelAux_nullity
  omega
theorem gateC:Fintype.card I * localRankBound 126 79970 39<
    coefficientCount 22901256 131071 79970 39:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelC_nullity
  omega
theorem gateThin:Fintype.card I * localRankBound 95 79970 29<
    coefficientCount 17266820 131071 79970 29:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelThin_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 97 2187 30<
    coefficientCount 17630332 131071 2187 30:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelB_nullity
  omega
theorem full_divisor_mem_box (D w L s m:ℕ)
    (gate:Fintype.card I * localRankBound m L s< coefficientCount D w L s)
    (u0 u1:I→ K) (F:P4)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1):
    F∈ globalCoefficientBox K D w L s:=by
  classical
  obtain ⟨a,ha,hk⟩:=exists_nonzero_kernel_array (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a≠ 0:=reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)
theorem full_A_divisor_mem_box (u0 u1:I→ K) (F:P4) (_hF:F≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 9996580 131071 79970 16 v.1):
    F∈ globalCoefficientBox K 9996580 131071 79970 16:=
  full_divisor_mem_box 9996580 131071 79970 16 55 gateA u0 u1 F hdiv
theorem full_Aux_divisor_mem_box (u0 u1:I→ K) (F:P4) (_hF:F≠ 0)
    (hdiv:∀ v:AuxKernel u0 u1,F ∣ reconstruct K 13086432 131071 79970 21 v.1):
    F∈ globalCoefficientBox K 13086432 131071 79970 21:=
  full_divisor_mem_box 13086432 131071 79970 21 72 gateAux u0 u1 F hdiv
theorem full_C_divisor_mem_box (u0 u1:I→ K) (F:P4) (_hF:F≠ 0)
    (hdiv:∀ v:CKernel u0 u1,F ∣ reconstruct K 22901256 131071 79970 39 v.1):
    F∈ globalCoefficientBox K 22901256 131071 79970 39:=
  full_divisor_mem_box 22901256 131071 79970 39 126 gateC u0 u1 F hdiv
theorem full_Thin_divisor_mem_box (u0 u1:I→ K) (F:P4) (_hF:F≠ 0)
    (hdiv:∀ v:ThinKernel u0 u1,F ∣ reconstruct K 17266820 131071 79970 29 v.1):
    F∈ globalCoefficientBox K 17266820 131071 79970 29:=
  full_divisor_mem_box 17266820 131071 79970 29 95 gateThin u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I→ K) (F:P4) (_hF:F≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 17630332 131071 2187 30 v.1):
    F∈ globalCoefficientBox K 17630332 131071 2187 30:=
  full_divisor_mem_box 17630332 131071 2187 30 97 gateB u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I→ K) (F:P4) (hF:F≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 9996580 131071 79970 16 v.1):
    wt residualYSWeights F≤ 73:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy:74≤ wt residualYSWeights F:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    9996580 131071 79970 16 (by decide)).mp hbox
  have hr:wt residualSWeights F≤ 16:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:9699238≤ wt (contactWeights 131071) F:=by omega
  have ht:74≤ wt residualTotalWeights F:=
    hy.trans (residual_weight_nested F).2
  have hdivK:∀ v:AKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        9996580 131071 79970 16 55 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:AKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          9996580 131071 79970 16 55 IRSProfile.domain u0 u1)
        F hdivK v∈ globalCoefficientBox K 297342 131071 79896 16:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      9996580 131071 79970 16 55 9699238 74 0
      IRSProfile.domain u0 u1 F hF hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 9996580-9699238=297342 by decide,
      show 79970-74=79896 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    9996580 131071 79970 16 55 297342 79896 16
    IRSProfile.domain u0 u1 F hF hdivK hq
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity,
    LocatorArithmetic.A_ys74_quotient_upper] at hobs
  omega
theorem common_A_slope_le (u0 u1:I→ K) (F:P4) (hF:F≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 9996580 131071 79970 16 v.1):
    wt residualSWeights F≤ 16:=
  ((mem_flagGlobalCoefficientBox_iff F 9996580 131071 79970 16 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_Thin_slope_le (u0 u1:I→ K) (F:P4) (hF:F≠ 0)
    (hdiv:∀ v:ThinKernel u0 u1,F ∣ reconstruct K 17266820 131071 79970 29 v.1):
    wt residualSWeights F≤ 29:=
  ((mem_flagGlobalCoefficientBox_iff F 17266820 131071 79970 29 (by decide)).mp
    (full_Thin_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_A_contact_le (u0 u1:I→ K) (F:P4) (hF:F≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 9996580 131071 79970 16 v.1):
    wt (contactWeights 131071) F≤ 9996579:=
  ((mem_flagGlobalCoefficientBox_iff F 9996580 131071 79970 16 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.2
theorem common_B_total_le (u0 u1:I→ K) (F:P4) (hF:F≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 17630332 131071 2187 30 v.1):
    wt residualTotalWeights F≤ 2184:=by
  by_contra hnot
  have ht:2185≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:BKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        17630332 131071 2187 30 97 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:BKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          17630332 131071 2187 30 97 IRSProfile.domain u0 u1)
        F hdivK v∈ globalCoefficientBox K 17630332 131071 2 30:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      17630332 131071 2187 30 97 0 2185 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 2187-2185=2 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    17630332 131071 2187 30 97 17630332 2 30
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelB_total_quotient_lt
end
end ProximityPrize.SubmissionLower.LocatorCaps
