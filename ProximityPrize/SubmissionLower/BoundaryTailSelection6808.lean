import ProximityPrize.SubmissionLower.BoundaryTailThresholdData6808
import ProximityPrize.SubmissionLower.BoundaryTailKernels80830

namespace ProximityPrize.SubmissionLower.Lower80830.Selection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid P4:=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 38619882 131071 8125 66 213 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20488482 131071 38915 35 113 IRSProfile.domain u0 u1
theorem gateTCap : Fintype.card I * localRankBound 213 8125 66 < coefficientCount 38619882 131071 8125 66 := by
  rw [Kernels80830.T.rank_exact, Kernels80830.T.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem gateB : Fintype.card I * localRankBound 113 38915 35 < coefficientCount 20488482 131071 38915 35 := by
  rw [Kernels80830.B.rank_exact, Kernels80830.B.coefficient_exact]
  norm_num [I, IRSProfile.Index]
private theorem gcd_mul_right_plain_associated
    (P H q:P4) (hc:IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
    have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
    have hcop:IsRelPrime (gcd P (H * q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
    (H q P:P4) (hc:IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
    have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
    have hcop:IsRelPrime (gcd (H * q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)
structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ globalCoefficientBox K 38619882 131071 8125 66
  QB_flag:QB ∈ globalCoefficientBox K 20488482 131071 38915 35
  common_divides_TCap:∀ v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 38619882 131071 8125 66 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 20488482 131071 38915 35 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181314 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaT,htT,hkT⟩:=exists_nonzero_kernel_array (I:=I)
    K 38619882 131071 8125 66 213 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 20488482 131071 38915 35 113 IRSProfile.domain u0 u1 gateB
  let vT0:TCapKernel u0 u1:=⟨thetaT,LinearMap.mem_ker.mpr hkT⟩
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (TCapKernel u0 u1):=⟨⟨vT0,0,by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT:=Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Module.Finite.finite_basis bT
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=bT.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HT:=commonGCD (TCapKernel u0 u1) bT
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHT:HT ≠ 0:=commonGCD_ne_zero (TCapKernel u0 u1) bT
  have hHB:HB ≠ 0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB ∈ globalCoefficientBox K 20488482 131071 38915 35:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 20488482 38915 35
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA:=commonQuotientLinear (TCapKernel u0 u1) bT hHT vA
  let QA:=submoduleReconstructLinear (TCapKernel u0 u1) vA
  have hQAeq:QA=HT * qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (TCapKernel u0 u1)) HT
    (commonDivisorProof (TCapKernel u0 u1) bT) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (TCapKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ globalCoefficientBox K 38619882 131071 8125 66:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 38619882 131071 8125 66 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 38619882 8125 66
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB:=submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq:QB=HB * qB:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB:QB ≠ 0:=by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB ∈ globalCoefficientBox K 20488482 131071 38915 35:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 20488482 131071 38915 35 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HT HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HT qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHT:gcd QA QB ∣ HT:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_TCap:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    exact hHHT.trans (commonGCD_dvd (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        38619882 131071 8125 66 213 181314 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide +kernel) (by decide +kernel) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        20488482 131071 38915 35 113 181314 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide +kernel) (by decide +kernel) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.Lower80830.Selection

namespace ProximityPrize.SubmissionLower.Lower80830.Caps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 19581912 131071 233846 32 108 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 38619882 131071 8125 66 213 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 20488482 131071 38915 35 113 IRSProfile.domain u0 u1
theorem gateA : Fintype.card I * localRankBound 108 233846 32 < coefficientCount 19581912 131071 233846 32 := by
  rw [Kernels80830.A.rank_exact, Kernels80830.A.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem gateTCap : Fintype.card I * localRankBound 213 8125 66 < coefficientCount 38619882 131071 8125 66 := by
  rw [Kernels80830.T.rank_exact, Kernels80830.T.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem gateB : Fintype.card I * localRankBound 113 38915 35 < coefficientCount 20488482 131071 38915 35 := by
  rw [Kernels80830.B.rank_exact, Kernels80830.B.coefficient_exact]
  norm_num [I, IRSProfile.Index]
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
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 19581912 131071 233846 32 v.1) :
    F ∈ globalCoefficientBox K 19581912 131071 233846 32:=
  full_divisor_mem_box 19581912 131071 233846 32 108 gateA u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20488482 131071 38915 35 v.1) :
    F ∈ globalCoefficientBox K 20488482 131071 38915 35:=
  full_divisor_mem_box 20488482 131071 38915 35 113 gateB u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 19581912 131071 233846 32 v.1) :
    wt residualYSWeights F ≤ 149:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    19581912 131071 233846 32 (by decide +kernel)).mp hbox
  have hr:wt residualSWeights F ≤ 32:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide +kernel)
  have hc:wt (contactWeights 131071) F ≤ 19581912:=by omega
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 19581912 131071 233846 32 v.1) :
    wt residualSWeights F ≤ 32:=
  ((mem_flagGlobalCoefficientBox_iff F 19581912 131071 233846 32 (by decide +kernel)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20488482 131071 38915 35 v.1) :
    wt residualSWeights F ≤ 35:=
  ((mem_flagGlobalCoefficientBox_iff F 20488482 131071 38915 35 (by decide +kernel)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 20488482 131071 38915 35 v.1) :
    wt residualYSWeights F ≤ 156:=by
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    20488482 131071 38915 35 (by decide +kernel)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr:wt residualSWeights F ≤ 35:=hcaps.2.1
  have hc:wt (contactWeights 131071) F ≤ 20488482 - 1:=hcaps.2.2
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide +kernel)
  omega
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 38619882 131071 8125 66 v.1) :
    wt residualTotalWeights F ≤ 8121:=by
  by_contra hnot
  have ht:8122 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        38619882 131071 8125 66 213 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          38619882 131071 8125 66 213 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 38619882 131071 3 66:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      38619882 131071 8125 66 213 0 8122 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 8125 - 8122=3 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    38619882 131071 8125 66 213 38619882 3 66
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  rw [Kernels80830.T.nullity_exact] at hobs
  exact (not_lt_of_ge hobs) Kernels80830.T.quotient_count_lt
end
end Caps
end ProximityPrize.SubmissionLower.Lower80830

namespace ProximityPrize.SubmissionLower.Lower80830.Selection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 8121:=
  Caps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 156:=
  Caps.common_B_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 35:=
  Caps.common_B_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
end
end ProximityPrize.SubmissionLower.Lower80830.Selection.SelectedPair
