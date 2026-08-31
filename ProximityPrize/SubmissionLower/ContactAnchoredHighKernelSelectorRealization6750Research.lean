import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientIntersection6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapChannelBridge6750Research
import ProximityPrize.SubmissionLower.ContactResidualContactDegree6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research
import ProximityPrize.SubmissionLower.ContactFlagKernelZeroExtension6750Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighKernelSelectorRealization6750Research

open scoped Classical BigOperators
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagKernelUniversalityResearch
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactAnchoredActualNullity6750Research
open ContactAnchoredHighKernelLowSlice6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapQuotientSupport6750Research
open ContactNestedFiveCapQuotientIntersection6750Research
open ContactNestedFiveCapChannelBridge6750Research
open ContactResidualContactDegree6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFlagKernelZeroExtension6750Research
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

universe u v

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 



theorem HardCell.selected_m61_high_kernel_slab_lt_finrank
    {I : Type v} [Fintype I]
    {t y r : Nat} (cell : HardCell t y r)
    (nodes u0 u1 : I → K) (hcard : Fintype.card I = domainSize) :
    cutWidth * residualChannels t y r (selectedTotal t y r) <
      Module.finrank K (LinearMap.ker
        (constraintMap K 14368046 131071 (selectedTotal t y r) 24 79
          nodes u0 u1)) := by
  have haffine : affineNullity (selectedTotal t y r) ≤
      actualNullity (selectedTotal t y r) :=
    affineNullity_le_actualNullity_of_base_le (by
      unfold selectedTotal
      exact Nat.le_add_right _ _)
  have hgap := cell.closes_actual_rank_gap haffine
  have hkernel := m61_high_constraintKernel_finrank_ge_actualNullity
    (K := K) (selectedTotal t y r) nodes u0 u1 hcard
  unfold actualRankGapHolds at hgap
  omega

 



theorem HardCell.exact_quotient_box_le_envelope
    {t y r c T YS S : Nat} (cell : HardCell t y r)
    (hcLower : contactSlope * y - r ≤ c) :
    nestedFiveCapCoefficientBox K (14317242 - c) 131071 T YS S ≤
      nestedFiveCapCoefficientBox K (quotientWeightedCut y r) 131071 T YS S := by
  apply nestedFiveCapCoefficientBox_mono_D K
  unfold quotientWeightedCut
  have hy := cell.y_lower
  have hr := cell.r_upper
  norm_num [familyMultiplicity, agreements, contactSlope, cutWidth] at *
  omega

 

theorem contact_le_47agreements_sub_one_of_dvd
    {L s : Nat} (H G : Poly4 K) (hG : G ≠ 0) (hdiv : H ∣ G)
    (hGbox : G ∈ ContactInterpolation.globalCoefficientBox K
      (48 * agreements) 131071 L s) :
    MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤
      48 * agreements - 1 := by
  have hcaps := (mem_globalCoefficientBox_iff G
    (48 * agreements) 131071 L s (by norm_num [agreements])).mp hGbox
  exact (weightedTotalDegree_le_of_dvd (contactWeights 131071)
    H G hdiv hG).trans hcaps.2.2

 







theorem HardCell.exists_selected_m61_low_quotient
    {I : Type v} [Fintype I]
    {t y r c : Nat} (cell : HardCell t y r)
    (nodes u0 u1 : I → K) (hcard : Fintype.card I = domainSize)
    (H : Poly4 K) (hH : H ≠ 0)
    (hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H = c)
    (hcUpper : c ≤ 48 * agreements - 1)
    (hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights H = t)
    (hHys : MvPolynomial.weightedTotalDegree residualYSWeights H = y)
    (hHs : MvPolynomial.weightedTotalDegree residualSWeights H = r)
    (hdiv : ∀ theta : LinearMap.ker
      (constraintMap K 14368046 131071 (selectedTotal t y r) 24 79
        nodes u0 u1),
      H ∣ reconstruct K 14368046 131071 (selectedTotal t y r) 24 theta.1) :
    ∃ theta : LinearMap.ker
        (constraintMap K 14368046 131071 (selectedTotal t y r) 24 79
          nodes u0 u1),
      theta ≠ 0 ∧
      ∃ Q : Poly4 K, Q ≠ 0 ∧
        H * Q = reconstruct K 14368046 131071
          (selectedTotal t y r) 24 theta.1 ∧
        Q ∈ nestedFiveCapCoefficientBox K
          (14317242 - c) 131071
          (selectedTotal t y r - t) (familyYSCap - y)
          (familySlopeCap - r) ∧
        Q ∈ nestedFiveCapCoefficientBox K
          (quotientWeightedCut y r) 131071
          (selectedTotal t y r - t) (familyYSCap - y)
          (familySlopeCap - r) ∧
        reconstruct K 14368046 131071 (selectedTotal t y r) 24 theta.1 ∈
          nestedFiveCapCoefficientBox K 14317242 131071
            (selectedTotal t y r) familyYSCap familySlopeCap := by
  classical
  let L := selectedTotal t y r
  let V := LinearMap.ker
    (constraintMap K 14368046 131071 L 24 79 nodes u0 u1)
  let recon : V →ₗ[K] Poly4 K :=
    (flagReconstructLinear (K := K) 14368046 131071 L 24).comp V.subtype
  have hrecon : Function.Injective recon := by
    intro a b hab
    apply Subtype.ext
    apply reconstruct_injective K 14368046 131071 L 24
    change reconstruct K 14368046 131071 L 24 a.1 =
      reconstruct K 14368046 131071 L 24 b.1 at hab
    exact hab
  have hdivV : ∀ v : V, H ∣ recon v := by
    intro v
    change H ∣ reconstruct K 14368046 131071 L 24 v.1
    simpa only [L, V] using hdiv v
  let qLin := mappedFixedFactorQuotientLinearMap H hH recon hdivV
  have hcLower : contactSlope * y - r ≤ c := by
    have h := residualYS_mul_sub_residualS_le_contact 131071 (by norm_num) H hH
    rw [hHys, hHs, hHcontact] at h
    simpa only [contactSlope] using h
  have hc : c ≤ 14317242 := by
    apply hcUpper.trans
    norm_num [agreements]
  have htL : t ≤ L := by
    have ht := cell.t_le_1692
    have hbase : familyBaseTotal ≤ L := by
      unfold L selectedTotal
      exact Nat.le_add_right _ _
    norm_num [familyBaseTotal] at hbase
    omega
  have hy84 : y ≤ familyYSCap := by
    have hy := cell.y_upper
    norm_num [familyYSCap] at *
    omega
  have hr18 : r ≤ familySlopeCap := by
    have hr := cell.r_upper
    norm_num [familySlopeCap] at *
    omega
  have hqimage : ∀ v : V, qLin v ∈
      nestedFiveCapCoefficientBox K
        (14368046 - c) 131071
        (L - t) (familyYSCap - y) (familySlopeCap - r) := by
    intro v
    rcases Classical.em (v = 0) with hv | hv
    · subst v
      change qLin (0 : V) ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · have hqv : qLin v ≠ 0 :=
        mappedFixedFactorQuotientLinearMap_ne_zero H hH recon hdivV
          hrecon hv
      apply quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
        hH hqv (mul_mappedFixedFactorQuotientLinearMap
          H hH recon hdivV v)
      · change reconstruct K 14368046 131071 L 24 v.1 ∈ _
        simpa only [familyYSCap, familySlopeCap] using
          reconstruct_mem_m61_high_fiveCap L v.1
      · exact hHcontact
      · exact hHtotal
      · exact hHys
      · exact hHs
  have hsource0 := HardCell.selected_m61_high_kernel_slab_lt_finrank
    cell nodes u0 u1 hcard
  have hsource :
      ((14368046 - c) - (14317242 - c)) *
        nestedFiveCapChannelCount (L - t)
          (familyYSCap - y) (familySlopeCap - r) <
        Module.finrank K V := by
    have hcut :
        (14368046 - c) - (14317242 - c) = cutWidth := by
      norm_num [cutWidth]
      omega
    change _ < Module.finrank K V
    rw [hcut, nestedFiveCapChannelCount_eq_channelCount]
    change cutWidth * residualChannels t y r L < Module.finrank K V
    exact hsource0
  have hDq : 14317242 - c ≤ 14368046 - c := by omega
  obtain ⟨theta, htheta, hQ, hQbox, hmul⟩ :=
    exists_nonzero_mappedFixedFactorQuotient_mem_low_nestedFiveCap K
      H hH recon hrecon hdivV
      (14368046 - c) (14317242 - c) 131071
      (L - t) (familyYSCap - y) (familySlopeCap - r)
      hDq hqimage hsource
  have hHBox : H ∈ nestedFiveCapCoefficientBox K
      (c + 1) 131071 t y r := by
    apply (mem_nestedFiveCapCoefficientBox_iff H
      (c + 1) 131071 t y r (by omega)).mpr
    rw [hHcontact, hHtotal, hHys, hHs]
    omega
  have hproductBox := nestedFiveCapCoefficientBox_mul K hHBox hQbox
  have hDsum :
      (c + 1) + (14317242 - c) - 1 = 14317242 := by
    omega
  have hTsum : t + (L - t) = L := by omega
  have hYsum : y + (familyYSCap - y) = familyYSCap := by omega
  have hSsum : r + (familySlopeCap - r) = familySlopeCap := by omega
  rw [hDsum, hTsum, hYsum, hSsum] at hproductBox
  have hmul' : H * qLin theta = reconstruct K 14368046 131071
      (selectedTotal t y r) 24 theta.1 := by
    change H * qLin theta = reconstruct K 14368046 131071 L 24 theta.1
    exact hmul
  have hproductBox' : reconstruct K 14368046 131071
      (selectedTotal t y r) 24 theta.1 ∈
        nestedFiveCapCoefficientBox K 14317242 131071
          (selectedTotal t y r) familyYSCap familySlopeCap := by
    rw [← hmul']
    simpa only [L] using hproductBox
  have hQenvelope : qLin theta ∈ nestedFiveCapCoefficientBox K
      (quotientWeightedCut y r) 131071 (L - t)
        (familyYSCap - y) (familySlopeCap - r) :=
    HardCell.exact_quotient_box_le_envelope (K := K) cell hcLower hQbox
  refine ⟨theta, htheta, qLin theta, hQ, ?_, ?_, ?_, ?_⟩
  · exact hmul'
  · simpa only [L] using hQbox
  · simpa only [L] using hQenvelope
  · exact hproductBox'

 


theorem specialization_pderiv_R_eq_zero_of_selected_m61_high_member
    [DecidableEq K] {I : Type v} [Fintype I] [DecidableEq I]
    (L : Nat) (nodes : I ↪ K) (u0 u1 : I → K)
    (theta : CoefficientIndex 14368046 131071 L 24 → K)
    (htheta : theta ∈ LinearMap.ker
      (constraintMap K 14368046 131071 L 24 79 nodes u0 u1))
    (hlow : reconstruct K 14368046 131071 L 24 theta ∈
      nestedFiveCapCoefficientBox K 14317242 131071 L 109 24)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ContactTranslation.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4)
        (reconstruct K 14368046 131071 L 24 theta)) = 0 := by
  have hordinary : reconstruct K 14368046 131071 L 24 theta ∈
      ContactInterpolation.globalCoefficientBox K 14317242 131071 L 24 := by
    intro d hd
    have h := hlow hd
    have htotal := h.1
    exact ⟨by omega, h.2.2.1, h.2.2.2⟩
  apply specialization_pderiv_R_eq_zero_of_high_kernel_and_low_box
    14368046 14317242 131071 L 24 79 nodes u0 u1 theta htheta
      hordinary P gamma support
  · norm_num
  · exact hP
  · omega
  · exact hvalues

end

end ContactAnchoredHighKernelSelectorRealization6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.HardCell.selected_m61_high_kernel_slab_lt_finrank
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.HardCell.exact_quotient_box_le_envelope
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.contact_le_47agreements_sub_one_of_dvd
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.HardCell.exists_selected_m61_low_quotient
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.specialization_pderiv_R_eq_zero_of_selected_m61_high_member
