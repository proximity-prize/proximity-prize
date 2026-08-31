import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research

 










namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighKernelSelectorRealization6750Research

open scoped Classical BigOperators
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagKernelUniversalityResearch
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
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

abbrev Poly4Shell (K : Type u) [Field K] := MvPolynomial (Fin 4) K

local instance firstDerivativeShellDecidable (t y r : Nat) :
    Decidable (FirstDerivativeShell t y r) := by
  unfold FirstDerivativeShell OrdinaryHardCell HardCell
  infer_instance

 
theorem FirstDerivativeShell.hardCell1658
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    HardCell 1658 y r := by
  exact cell.false.elim

theorem FirstDerivativeShell.selector_inputs
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    t ≤ familyBaseTotal ∧
      familyYSCap - y ≤ familyBaseTotal - t ∧
      0 < selectorSlope y r := by
  exact cell.false.elim

theorem FirstDerivativeShell.selectorDeficit_le_max
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    selectorDeficit t y r ≤
      selectorSlope y r * (familyMaxTotal - familyBaseTotal) := by
  exact cell.false.elim

theorem FirstDerivativeShell.selectedTotal_le_4186
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    selectedTotal t y r ≤ familyMaxTotal :=
  cell.false.elim

theorem FirstDerivativeShell.quotient_caps
    {t y r : Nat} (cell : FirstDerivativeShell t y r) :
    selectedTotal t y r - t ≤ 2530 ∧
      familyYSCap - y ≤ 46 ∧
      familySlopeCap - r ≤ 10 ∧
      2524503 ≤ quotientWeightedCut y r := by
  exact cell.false.elim

theorem FirstDerivativeShell.closes_actual_rank_gap
    {t y r : Nat} (cell : FirstDerivativeShell t y r)
    (hnullity : affineNullity (selectedTotal t y r) ≤
      actualNullity (selectedTotal t y r)) :
    actualRankGapHolds t y r (selectedTotal t y r) :=
  cell.false.elim

theorem FirstDerivativeShell.selected_m61_high_kernel_slab_lt_finrank
    {I : Type v} [Fintype I]
    {t y r : Nat} (cell : FirstDerivativeShell t y r)
    (nodes u0 u1 : I → K) (hcard : Fintype.card I = domainSize) :
    cutWidth * residualChannels t y r (selectedTotal t y r) <
      Module.finrank K (LinearMap.ker
        (constraintMap K 11094924 131071 (selectedTotal t y r) 18 61
          nodes u0 u1)) := by
  exact cell.false.elim

theorem FirstDerivativeShell.exact_quotient_box_le_envelope
    {t y r c T YS S : Nat} (cell : FirstDerivativeShell t y r)
    (hcLower : contactSlope * y - r ≤ c) :
    nestedFiveCapCoefficientBox K (11044110 - c) 131071 T YS S ≤
      nestedFiveCapCoefficientBox K (quotientWeightedCut y r) 131071 T YS S :=
  cell.false.elim

 



theorem FirstDerivativeShell.exists_selected_m61_low_quotient
    {I : Type v} [Fintype I]
    {t y r c : Nat} (cell : FirstDerivativeShell t y r)
    (nodes u0 u1 : I → K) (hcard : Fintype.card I = domainSize)
    (H : Poly4Shell K) (hH : H ≠ 0)
    (hHcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) H = c)
    (hcUpper : c ≤ 47 * agreements - 1)
    (hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights H = t)
    (hHys : MvPolynomial.weightedTotalDegree residualYSWeights H = y)
    (hHs : MvPolynomial.weightedTotalDegree residualSWeights H = r)
    (hdiv : ∀ theta : LinearMap.ker
      (constraintMap K 11094924 131071 (selectedTotal t y r) 18 61
        nodes u0 u1),
      H ∣ reconstruct K 11094924 131071 (selectedTotal t y r) 18 theta.1) :
    ∃ theta : LinearMap.ker
        (constraintMap K 11094924 131071 (selectedTotal t y r) 18 61
          nodes u0 u1),
      theta ≠ 0 ∧
      ∃ Q : Poly4Shell K, Q ≠ 0 ∧
        H * Q = reconstruct K 11094924 131071
          (selectedTotal t y r) 18 theta.1 ∧
        Q ∈ nestedFiveCapCoefficientBox K
          (11044110 - c) 131071
          (selectedTotal t y r - t) (familyYSCap - y)
          (familySlopeCap - r) ∧
        Q ∈ nestedFiveCapCoefficientBox K
          (quotientWeightedCut y r) 131071
          (selectedTotal t y r - t) (familyYSCap - y)
          (familySlopeCap - r) ∧
        reconstruct K 11094924 131071 (selectedTotal t y r) 18 theta.1 ∈
          nestedFiveCapCoefficientBox K 11044110 131071
            (selectedTotal t y r) familyYSCap familySlopeCap := by
  exact cell.false.elim
  /-
  classical
  let L := selectedTotal t y r
  let V := LinearMap.ker
    (constraintMap K 11094924 131071 L 18 61 nodes u0 u1)
  let recon : V →ₗ[K] Poly4Shell K :=
    (flagReconstructLinear (K := K) 11094924 131071 L 18).comp V.subtype
  have hrecon : Function.Injective recon := by
    intro a b hab
    apply Subtype.ext
    apply reconstruct_injective K 11094924 131071 L 18
    change reconstruct K 11094924 131071 L 18 a.1 =
      reconstruct K 11094924 131071 L 18 b.1 at hab
    exact hab
  have hdivV : ∀ v : V, H ∣ recon v := by
    intro v
    change H ∣ reconstruct K 11094924 131071 L 18 v.1
    simpa only [L, V] using hdiv v
  let qLin := mappedFixedFactorQuotientLinearMap H hH recon hdivV
  have hcLower : contactSlope * y - r ≤ c := by
    have h := residualYS_mul_sub_residualS_le_contact 131071 (by norm_num) H hH
    rw [hHys, hHs, hHcontact] at h
    simpa only [contactSlope] using h
  have hc : c ≤ 11044110 := by
    apply hcUpper.trans
    norm_num [agreements]
  have htL : t ≤ L := by
    have ht := cell.eq_1659_and_r_le.1
    have hbase : familyBaseTotal ≤ L := by
      unfold L selectedTotal
      exact Nat.le_add_right _ _
    norm_num [familyBaseTotal] at hbase
    omega
  have hy84 : y ≤ familyYSCap := by
    have hy := cell.1.2.1
    norm_num [familyYSCap] at *
    omega
  have hr18 : r ≤ familySlopeCap := by
    have hr := cell.1.2.2.2.1
    norm_num [familySlopeCap] at *
    omega
  have hqimage : ∀ v : V, qLin v ∈
      nestedFiveCapCoefficientBox K
        (11094924 - c) 131071
        (L - t) (familyYSCap - y) (familySlopeCap - r) := by
    intro v
    rcases Classical.em (v = 0) with hv | hv
    · subst v
      change qLin (0 : V) ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · have hqv : qLin v ≠ 0 :=
        mappedFixedFactorQuotientLinearMap_ne_zero H hH recon hdivV hrecon hv
      apply quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
        hH hqv (mul_mappedFixedFactorQuotientLinearMap H hH recon hdivV v)
      · change reconstruct K 11094924 131071 L 18 v.1 ∈ _
        simpa only [familyYSCap, familySlopeCap] using
          reconstruct_mem_m61_high_fiveCap L v.1
      · exact hHcontact
      · exact hHtotal
      · exact hHys
      · exact hHs
  have hsource0 :=
    FirstDerivativeShell.selected_m61_high_kernel_slab_lt_finrank
      cell nodes u0 u1 hcard
  have hsource :
      ((11094924 - c) - (11044110 - c)) *
        nestedFiveCapChannelCount (L - t)
          (familyYSCap - y) (familySlopeCap - r) <
        Module.finrank K V := by
    have hcut : (11094924 - c) - (11044110 - c) = cutWidth := by
      norm_num [cutWidth]
      omega
    change _ < Module.finrank K V
    rw [hcut, nestedFiveCapChannelCount_eq_channelCount]
    change cutWidth * residualChannels t y r L < Module.finrank K V
    exact hsource0
  have hDq : 11044110 - c ≤ 11094924 - c := by omega
  obtain ⟨theta, htheta, hQ, hQbox, hmul⟩ :=
    exists_nonzero_mappedFixedFactorQuotient_mem_low_nestedFiveCap K
      H hH recon hrecon hdivV
      (11094924 - c) (11044110 - c) 131071
      (L - t) (familyYSCap - y) (familySlopeCap - r)
      hDq hqimage hsource
  have hHBox : H ∈ nestedFiveCapCoefficientBox K (c + 1) 131071 t y r := by
    apply (mem_nestedFiveCapCoefficientBox_iff H
      (c + 1) 131071 t y r (by omega)).mpr
    rw [hHcontact, hHtotal, hHys, hHs]
    omega
  have hproductBox := nestedFiveCapCoefficientBox_mul K hHBox hQbox
  have hDsum : (c + 1) + (11044110 - c) - 1 = 11044110 := by omega
  have hTsum : t + (L - t) = L := by omega
  have hYsum : y + (familyYSCap - y) = familyYSCap := by omega
  have hSsum : r + (familySlopeCap - r) = familySlopeCap := by omega
  rw [hDsum, hTsum, hYsum, hSsum] at hproductBox
  have hmul' : H * qLin theta = reconstruct K 11094924 131071
      (selectedTotal t y r) 18 theta.1 := by
    change H * qLin theta = reconstruct K 11094924 131071 L 18 theta.1
    exact hmul
  have hproductBox' : reconstruct K 11094924 131071
      (selectedTotal t y r) 18 theta.1 ∈
        nestedFiveCapCoefficientBox K 11044110 131071
          (selectedTotal t y r) familyYSCap familySlopeCap := by
    rw [← hmul']
    simpa only [L] using hproductBox
  have hQenvelope : qLin theta ∈ nestedFiveCapCoefficientBox K
      (quotientWeightedCut y r) 131071 (L - t)
        (familyYSCap - y) (familySlopeCap - r) :=
    FirstDerivativeShell.exact_quotient_box_le_envelope cell hcLower hQbox
  refine ⟨theta, htheta, qLin theta, hQ, hmul', ?_, ?_, hproductBox'⟩
  · simpa only [L] using hQbox
  · simpa only [L] using hQenvelope
  -/

end

end ContactAnchoredHighKernelSelectorRealization6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.FirstDerivativeShell.hardCell1658
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research.FirstDerivativeShell.exists_selected_m61_low_quotient
