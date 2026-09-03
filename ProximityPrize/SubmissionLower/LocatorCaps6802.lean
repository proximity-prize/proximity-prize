import ProximityPrize.SubmissionLower.LocatorSelection6802

namespace ProximityPrize.SubmissionLower.LocatorCaps6802

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 17411808 131071 130000 29 96
    IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 33916751 131071 6408 58 187
    IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 19588284 131071 15200 32 108
    IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 96 130000 29 <
    coefficientCount 17411808 131071 130000 29 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic6802.kernelA_nullity
  omega

theorem gateTCap : Fintype.card I * localRankBound 187 6408 58 <
    coefficientCount 33916751 131071 6408 58 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic6802.kernelTCap_nullity
  omega

theorem gateB : Fintype.card I * localRankBound 108 15200 32 <
    coefficientCount 19588284 131071 15200 32 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := LocatorArithmetic6802.kernelB_nullity
  omega

theorem full_divisor_mem_box (D w L s m : ℕ)
    (gate : Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1 : I → K) (F : P4)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m
      IRSProfile.domain u0 u1, F ∣ reconstruct K D w L s v.1) :
    F ∈ globalCoefficientBox K D w L s := by
  classical
  obtain ⟨a, ha, hk⟩ := exists_nonzero_kernel_array (I := I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v : ConstraintKernel (K := K) D w L s m IRSProfile.domain u0 u1 :=
    ⟨a, LinearMap.mem_ker.mpr hk⟩
  have hQ : reconstruct K D w L s a ≠ 0 :=
    reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)

theorem full_A_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 17411808 131071 130000 29 v.1) :
    F ∈ globalCoefficientBox K 17411808 131071 130000 29 :=
  full_divisor_mem_box 17411808 131071 130000 29 96 gateA u0 u1 F hdiv

theorem full_TCap_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : TCapKernel u0 u1,
      F ∣ reconstruct K 33916751 131071 6408 58 v.1) :
    F ∈ globalCoefficientBox K 33916751 131071 6408 58 :=
  full_divisor_mem_box 33916751 131071 6408 58 187 gateTCap u0 u1 F hdiv

theorem full_B_divisor_mem_box (u0 u1 : I → K) (F : P4) (_hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      F ∣ reconstruct K 19588284 131071 15200 32 v.1) :
    F ∈ globalCoefficientBox K 19588284 131071 15200 32 :=
  full_divisor_mem_box 19588284 131071 15200 32 108 gateB u0 u1 F hdiv

theorem common_A_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 17411808 131071 130000 29 v.1) :
    wt residualYSWeights F ≤ 132 := by
  have hbox := full_A_divisor_mem_box u0 u1 F hF hdiv
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    17411808 131071 130000 29 (by decide)).mp hbox
  have hr : wt residualSWeights F ≤ 29 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  have hc : wt (contactWeights 131071) F ≤ 17411808 := by omega
  omega

theorem common_A_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : AKernel u0 u1,
      F ∣ reconstruct K 17411808 131071 130000 29 v.1) :
    wt residualSWeights F ≤ 29 :=
  ((mem_flagGlobalCoefficientBox_iff F 17411808 131071 130000 29 (by decide)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1

theorem common_B_slope_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      F ∣ reconstruct K 19588284 131071 15200 32 v.1) :
    wt residualSWeights F ≤ 32 :=
  ((mem_flagGlobalCoefficientBox_iff F 19588284 131071 15200 32 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1

theorem common_B_ys_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      F ∣ reconstruct K 19588284 131071 15200 32 v.1) :
    wt residualYSWeights F ≤ 149 := by
  have hcaps := (mem_flagGlobalCoefficientBox_iff F
    19588284 131071 15200 32 (by decide)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr : wt residualSWeights F ≤ 32 := hcaps.2.1
  have hc : wt (contactWeights 131071) F ≤ 19588284 - 1 := hcaps.2.2
  have hw := residualYS_mul_le_contact_add_slope F 131071 (by decide)
  omega

theorem common_TCap_total_le (u0 u1 : I → K) (F : P4) (hF : F ≠ 0)
    (hdiv : ∀ v : TCapKernel u0 u1,
      F ∣ reconstruct K 33916751 131071 6408 58 v.1) :
    wt residualTotalWeights F ≤ 6403 := by
  by_contra hnot
  have ht : 6404 ≤ wt residualTotalWeights F := by omega
  have hdivK : ∀ v : TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K := K)
        33916751 131071 6408 58 187 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq : ∀ v : TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K := K) (I := I)
          33916751 131071 6408 58 187 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 33916751 131071 4 58 := by
    have h := LocatorLowQuotient.quotient_box_of_full_divisor (K := K) (I := I)
      33916751 131071 6408 58 187 0 6404 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero, show 6408 - 6404 = 4 by decide] using h v
  have hobs := common_divisor_dimension_obstruction (K := K) (I := I)
    33916751 131071 6408 58 187 33916751 4 58
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]] at hobs
  exact (not_lt_of_ge hobs) LocatorArithmetic6802.kernelTCap_total_quotient_lt

end

end ProximityPrize.SubmissionLower.LocatorCaps6802

namespace ProximityPrize.SubmissionLower.LocatorSelection6802.SelectedPair

open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 6403 :=
  LocatorCaps6802.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap

theorem common_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 149 :=
  LocatorCaps6802.common_B_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

theorem common_slope_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 32 :=
  LocatorCaps6802.common_B_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

end

end ProximityPrize.SubmissionLower.LocatorSelection6802.SelectedPair
