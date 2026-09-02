import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorCaps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 600000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
/-! Row 6786.  Three kernels feed the caps: the A kernel `(76, 130000, 22)`
gives the narrow per-factor caps (ys `101`, slope `22`) for the factors that
divide every A reconstruction; the B kernel `(80, 16000, 23)` gives the caps of
the whole common divisor (slope `23`, ys `110`); the total-cap kernel
`(145, 3923, 45)` gives its total `3922`. -/
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 13794760 131071 130000 22 76 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 25592910 131071 4100 43 141 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 14883820 131071 13000 24 82 IRSProfile.domain u0 u1
theorem gateA:Fintype.card I * localRankBound 76 130000 22 <
    coefficientCount 13794760 131071 130000 22:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelA_nullity
  omega
theorem gateTCap:Fintype.card I * localRankBound 141 4100 43 <
    coefficientCount 25592910 131071 4100 43:=by
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]]
  have h:=LocatorArithmetic.kernelTCap_nullity
  omega
theorem gateB:Fintype.card I * localRankBound 82 13000 24 <
    coefficientCount 14883820 131071 13000 24:=by
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
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 13794760 131071 130000 22 v.1) :
    F ∈ globalCoefficientBox K 13794760 131071 130000 22:=
  full_divisor_mem_box 13794760 131071 130000 22 76 gateA u0 u1 F hdiv
theorem full_TCap_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 25592910 131071 4100 43 v.1) :
    F ∈ globalCoefficientBox K 25592910 131071 4100 43:=
  full_divisor_mem_box 25592910 131071 4100 43 141 gateTCap u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 14883820 131071 13000 24 v.1) :
    F ∈ globalCoefficientBox K 14883820 131071 13000 24:=
  full_divisor_mem_box 14883820 131071 13000 24 82 gateB u0 u1 F hdiv
/-- A divisor of every A reconstruction has ys weight at most `103`: a divisor
of ys weight `104` would leave a quotient in the box
`(163398, 129896, 22)` of dimension `29623335886 < 39341215191`. -/
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 13794760 131071 130000 22 v.1) :
    wt residualYSWeights F ≤ 103:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  by_contra hnot
  have hy:104 ≤ wt residualYSWeights F:=by omega
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    13794760 131071 130000 22 (by decide)).mp hbox
  have hr:wt residualSWeights F ≤ 22:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc:13631362 ≤ wt (contactWeights 131071) F:=by omega
  have ht:104 ≤ wt residualTotalWeights F:=
    hy.trans (residual_weight_nested F).2
  have hdivK:∀ v:AKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        13794760 131071 130000 22 76 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:AKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          13794760 131071 130000 22 76 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 163398 131071 129896 22:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      13794760 131071 130000 22 76 13631362 104 0
      IRSProfile.domain u0 u1 F hF hdivK hc ht (Nat.zero_le _)
    intro v
    simpa only [show 13794760 - 13631362=163398 by decide,
      show 130000 - 104=129896 by decide,Nat.sub_zero] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    13794760 131071 130000 22 76 163398 129896 22
    IRSProfile.domain u0 u1 F hF hdivK hq
  simp only [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index],
    LocatorArithmetic.kernelA_nullity,
    LocatorArithmetic.A_ys103_quotient_upper] at hobs
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 13794760 131071 130000 22 v.1) :
    wt residualSWeights F ≤ 22:=
  ((mem_flagGlobalCoefficientBox_iff F 13794760 131071 130000 22 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 14883820 131071 13000 24 v.1) :
    wt residualSWeights F ≤ 24:=
  ((mem_flagGlobalCoefficientBox_iff F 14883820 131071 13000 24 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 14883820 131071 13000 24 v.1) :
    wt residualYSWeights F ≤ 113:=by
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    14883820 131071 13000 24 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr:wt residualSWeights F ≤ 24:=hcaps.2.1
  have hc:wt (contactWeights 131071) F ≤ 14883820 - 1:=hcaps.2.2
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide)
  omega
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 25592910 131071 4100 43 v.1) :
    wt residualTotalWeights F ≤ 4099:=by
  by_contra hnot
  have ht:4100 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        25592910 131071 4100 43 141 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          25592910 131071 4100 43 141 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 25592910 131071 0 43:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      25592910 131071 4100 43 141 0 4100 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 4100 - 4100=0 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    25592910 131071 4100 43 141 25592910 0 43
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic.kernelTCap_total_quotient_lt
end
end LocatorCaps
