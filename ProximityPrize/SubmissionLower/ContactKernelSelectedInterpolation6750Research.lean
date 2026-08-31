import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelGenericChoice6750Research
import ProximityPrize.SubmissionLower.ContactKernelCommonGCDTotal6750Research
import ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research

 







namespace ProximityPrize.SubmissionLower.ContactKernelSelectedInterpolation6750Research

open scoped Classical BigOperators
open Set UniqueFactorizationMonoid
open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagKernelUniversalityResearch
open ContactKernelCommonGCD6750Research
open ContactKernelCommonGCD6750Research.E80260
open ContactKernelGenericChoice6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactGeometricFactorCover ContactGCDCumulativeFlagsResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactFactorCaps ContactRecursiveGCDResearch
open ContactStackedGCDCover6670Research
open ContactTwoTailParameters6750Research

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev GlobalPoly := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : StrongNormalizationMonoid GlobalPoly :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

 

structure SelectedInterpolants6750Source (u0 u1 : I → K) where
  QA : GlobalPoly
  QB : GlobalPoly
  QC : GlobalPoly
  QA_ne_zero : QA ≠ 0
  QB_ne_zero : QB ≠ 0
  QC_ne_zero : QC ≠ 0
  QA_mem : QA ∈ globalCoefficientBox K
    profileA.weightedCap w profileA.totalCap profileA.slopeCap
  QB_mem : QB ∈ globalCoefficientBox K
    profileB.weightedCap w profileB.totalCap profileB.slopeCap
  QC_mem : QC ∈ globalCoefficientBox K
    profileC.weightedCap w profileC.totalCap profileC.slopeCap
  gcd12_mem : gcd12 QA QB ∈ globalCoefficientBox K
    profileA.weightedCap w 1698 profileA.slopeCap
  oldCore_ys_le :
    MvPolynomial.weightedTotalDegree residualYSWeights (gcd123 QA QB QC) ≤ 65
  oldCore_dvd_B : ∀ v : BKernel u0 u1,
    gcd123 QA QB QC ∣
      reconstruct K 17096156 131071 1700 29 v.1
  universal_cover : ∀ gamma P (support : Finset I),
    P.natDegree ≤ w → agreements ≤ support.card →
    (∀ i ∈ support,
      P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
    RecursiveSpecializationBranch P gamma QA QB QC

theorem field_cardinality :
    Fintype.card K = (2130706433 : Nat) ^ 6 := by
  norm_num [K, IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem normalizedFactorSet_card_lt_field_of_mem_flagBox
    (P : GlobalPoly) (D L s : Nat) (hP : P ≠ 0)
    (hbox : P ∈ globalCoefficientBox K D 131071 L s)
    (hsmall : (D - 1) + (D - 1) / 131071 + s + L <
      (2130706433 : Nat) ^ 6) :
    (normalizedFactorSet P).card < ENat.card K := by
  have hle := normalizedFactorSet_card_le_of_mem_flagBox
    P D 131071 L s (by decide) hP hbox
  rw [ENat.card_eq_coe_fintype_card, field_cardinality]
  exact_mod_cast hle.trans_lt hsmall

theorem commonGCDAtMax_mem_flagBox
    {D L s : Nat}
    (V : Submodule K (CoefficientIndex D 131071 L s → K))
    {beta : Type*} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta K V) :
    commonGCDAtMax V b ∈ globalCoefficientBox K D 131071 L s := by
  let i : beta := Classical.choice inferInstance
  let Q := reconstruct K D 131071 L s (b i).1
  have hQ : Q ≠ 0 := by
    apply reconstruct_ne_zero K D 131071 L s
    intro hb
    apply b.ne_zero i
    exact Subtype.ext hb
  exact mem_flagGlobalCoefficientBox_of_dvd (commonGCDAtMax V b) Q
    D 131071 L s hQ (commonGCDAtMax_dvd_basis V b i)
    (reconstruct_mem_globalCoefficientBox K D 131071 L s (b i).1)

private theorem gcd_mul_left_plain_associated
    (H q P : GlobalPoly) (hc : IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd (H * q) P ∣ H * q := gcd_dvd_left (H * q) P
    have hright : gcd (H * q) P ∣ P := gcd_dvd_right (H * q) P
    have hcop : IsRelPrime (gcd (H * q) P) q :=
      hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd
      ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)

private theorem gcd_mul_right_plain_associated
    (P H q : GlobalPoly) (hc : IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd P (H * q) ∣ P := gcd_dvd_left P (H * q)
    have hright : gcd P (H * q) ∣ H * q := gcd_dvd_right P (H * q)
    have hcop : IsRelPrime (gcd P (H * q)) q :=
      hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))

 
theorem exists_selected_interpolants_of_profileB_cap
    (hBcap : ∀ (u0 u1 : I → K)
      {beta : Type} [Fintype beta] [Nonempty beta]
      (b : Module.Basis beta K (BKernel u0 u1)),
      MvPolynomial.weightedTotalDegree residualTotalWeights
        (commonGCDAtMax (BKernel u0 u1) b) ≤ 1698)
    (u0 u1 : I → K) :
    Nonempty (SelectedInterpolants6750Source u0 u1) := by
  classical
  obtain ⟨thetaA, hthetaA, hkernelA⟩ := exists_nonzero_kernel_array
    K 8729952 131071 40500 14 48 IRSProfile.domain u0 u1
      profileA_interpolation_gate
  obtain ⟨thetaB, hthetaB, hkernelB⟩ := exists_nonzero_kernel_array
    K 17096156 131071 1700 29 94 IRSProfile.domain u0 u1
      profileB_interpolation_gate
  let vA0 : AKernel u0 u1 := ⟨thetaA, LinearMap.mem_ker.mpr hkernelA⟩
  let vB0 : BKernel u0 u1 := ⟨thetaB, LinearMap.mem_ker.mpr hkernelB⟩
  letI : Nontrivial (AKernel u0 u1) := ⟨⟨vA0, 0, by
    intro h
    apply hthetaA
    exact congrArg Subtype.val h⟩⟩
  letI : Nontrivial (BKernel u0 u1) := ⟨⟨vB0, 0, by
    intro h
    apply hthetaB
    exact congrArg Subtype.val h⟩⟩
  let bA := Module.Free.chooseBasis K (AKernel u0 u1)
  let bB := Module.Free.chooseBasis K (BKernel u0 u1)
  letI : Finite (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) :=
    Module.Finite.finite_basis bA
  letI : Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI : Fintype (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) :=
    Fintype.ofFinite _
  letI : Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Fintype.ofFinite _
  letI : Nonempty (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) :=
    bA.index_nonempty
  letI : Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    bB.index_nonempty
  let HA := commonGCDAtMax (AKernel u0 u1) bA
  let HB := commonGCDAtMax (BKernel u0 u1) bB
  have hHA : HA ≠ 0 := by
    dsimp only [HA]
    exact commonGCDAtMax_ne_zero (AKernel u0 u1) bA
  have hHB : HB ≠ 0 := by
    dsimp only [HB]
    exact commonGCDAtMax_ne_zero (BKernel u0 u1) bB
  have hHBbox : HB ∈ globalCoefficientBox K 17096156 131071 1700 29 := by
    dsimp only [HB]
    exact commonGCDAtMax_mem_flagBox (BKernel u0 u1) bB
  have hcardHB : (normalizedFactorSet HB).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 17096156 1700 29
      hHB hHBbox (by norm_num)
  obtain ⟨vA, hvA, hcopA⟩ := exists_common_quotient_isRelPrime
    8729952 131071 40500 14 48 IRSProfile.domain u0 u1
      bA hHA HB hHB hcardHB
  let qA := commonQuotientLinear
    8729952 131071 40500 14 48 IRSProfile.domain u0 u1 bA hHA vA
  let QA := kernelReconstructLinear
    8729952 131071 40500 14 48 IRSProfile.domain u0 u1 vA
  have hQAeq : QA = HA * qA := by
    exact (mul_commonQuotientLinear
      8729952 131071 40500 14 48 IRSProfile.domain u0 u1 bA hHA vA).symm
  have hQA : QA ≠ 0 := by
    intro hz
    apply hvA
    apply kernelReconstructLinear_injective
      8729952 131071 40500 14 48 IRSProfile.domain u0 u1
    simpa only [map_zero, QA] using hz
  have hQAbox : QA ∈ globalCoefficientBox K 8729952 131071 40500 14 := by
    dsimp only [QA]
    rw [kernelReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K
      8729952 131071 40500 14 vA.1
  have hcardQA : (normalizedFactorSet QA).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 8729952 40500 14
      hQA hQAbox (by norm_num)
  obtain ⟨vB, hvB, hcopB⟩ := exists_common_quotient_isRelPrime
    17096156 131071 1700 29 94 IRSProfile.domain u0 u1
      bB hHB QA hQA hcardQA
  let qB := commonQuotientLinear
    17096156 131071 1700 29 94 IRSProfile.domain u0 u1 bB hHB vB
  let QB := kernelReconstructLinear
    17096156 131071 1700 29 94 IRSProfile.domain u0 u1 vB
  have hQBeq : QB = HB * qB := by
    exact (mul_commonQuotientLinear
      17096156 131071 1700 29 94 IRSProfile.domain u0 u1 bB hHB vB).symm
  have hQB : QB ≠ 0 := by
    intro hz
    apply hvB
    apply kernelReconstructLinear_injective
      17096156 131071 1700 29 94 IRSProfile.domain u0 u1
    simpa only [map_zero, QB] using hz
  have hQBbox : QB ∈ globalCoefficientBox K 17096156 131071 1700 29 := by
    dsimp only [QB]
    rw [kernelReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K
      17096156 131071 1700 29 vB.1
  have hAssocA : Associated (gcd QA HB) (gcd HA HB) := by
    have h := gcd_mul_left_plain_associated HA qA HB
      (by simpa only [qA] using hcopA)
    rwa [← hQAeq] at h
  have hAssocB : Associated (gcd QA QB) (gcd QA HB) := by
    have h := gcd_mul_right_plain_associated QA HB qB
      (by simpa only [qB] using hcopB)
    rwa [← hQBeq] at h
  let H := gcd QA QB
  have hAssocH : Associated H (gcd HA HB) := hAssocB.trans hAssocA
  have hH : H ≠ 0 := by
    intro hz
    have hz' : gcd QA QB = 0 := by simpa only [H] using hz
    exact hQA ((gcd_eq_zero_iff QA QB).mp hz').1
  have hHHA : H ∣ HA :=
    hAssocH.dvd_iff_dvd_left.mpr (gcd_dvd_left HA HB)
  have hHHB : H ∣ HB :=
    hAssocH.dvd_iff_dvd_left.mpr (gcd_dvd_right HA HB)
  have hHdivA : ∀ v : AKernel u0 u1,
      H ∣ reconstruct K 8729952 131071 40500 14 v.1 := by
    intro v
    exact hHHA.trans (commonGCDAtMax_dvd (AKernel u0 u1) bA v)
  have hHdivB : ∀ v : BKernel u0 u1,
      H ∣ reconstruct K 17096156 131071 1700 29 v.1 := by
    intro v
    exact hHHB.trans (commonGCDAtMax_dvd (BKernel u0 u1) bB v)
  have hHboxA : H ∈ globalCoefficientBox K 8729952 131071 40500 14 :=
    mem_flagGlobalCoefficientBox_of_dvd H QA 8729952 131071 40500 14
      hQA (by dsimp only [H]; exact gcd_dvd_left QA QB) hQAbox
  let QC := QA
  let G := gcd H QC
  have hQC : QC ≠ 0 := by simpa only [QC] using hQA
  have hG : G ≠ 0 := by
    intro hz
    have hz' : gcd H QC = 0 := by simpa only [G] using hz
    exact hH ((gcd_eq_zero_iff H QC).mp hz').1
  have hGH : G ∣ H := by
    dsimp only [G]
    exact gcd_dvd_left H QC
  have hGboxA : G ∈ globalCoefficientBox K 8729952 131071 40500 14 :=
    mem_flagGlobalCoefficientBox_of_dvd G H 8729952 131071 40500 14
      hH hGH hHboxA
  have hHAys : MvPolynomial.weightedTotalDegree residualYSWeights HA ≤ 65 := by
    dsimp only [HA]
    exact profileA_commonGCD_ys_le u0 u1 bA
  have hHAtSlope :
      MvPolynomial.weightedTotalDegree residualSWeights HA ≤ 14 := by
    dsimp only [HA]
    exact profileA_commonGCD_slope_le u0 u1 bA
  have hHBtotal :
      MvPolynomial.weightedTotalDegree residualTotalWeights HB ≤ 1698 := by
    dsimp only [HB]
    exact hBcap u0 u1 bB
  have hHtotal : MvPolynomial.weightedTotalDegree residualTotalWeights H ≤ 1698 :=
    (weightedTotalDegree_le_of_dvd residualTotalWeights H HB hHHB hHB).trans
      hHBtotal
  have hGys : MvPolynomial.weightedTotalDegree residualYSWeights G ≤ 65 :=
    (weightedTotalDegree_le_of_dvd residualYSWeights G HA
      (hGH.trans hHHA) hHA).trans hHAys
  have hGslope : MvPolynomial.weightedTotalDegree residualSWeights G ≤ 14 :=
    (weightedTotalDegree_le_of_dvd residualSWeights G HA
      (hGH.trans hHHA) hHA).trans hHAtSlope
  have hHbox1666 : H ∈ globalCoefficientBox K 8729952 131071 1698 14 := by
    have hcaps := (mem_flagGlobalCoefficientBox_iff H
      8729952 131071 40500 14 (by decide)).mp hHboxA
    exact (mem_flagGlobalCoefficientBox_iff H
      8729952 131071 1698 14 (by decide)).mpr
        ⟨hHtotal, hcaps.2⟩
  have hvAcoeff : vA.1 ≠ 0 := by
    intro hz
    apply hvA
    exact Subtype.ext hz
  have hvBcoeff : vB.1 ≠ 0 := by
    intro hz
    apply hvB
    exact Subtype.ext hz
  have hUnivA := (nonzero_kernel_member_universal K
    8729952 131071 40500 14 48 agreements IRSProfile.domain u0 u1
    vA.1 hvAcoeff vA.2 (by norm_num [agreements, n, errors])
      (by norm_num [agreements, n, errors])).2.2
  have hUnivB := (nonzero_kernel_member_universal K
    17096156 131071 1700 29 94 agreements IRSProfile.domain u0 u1
    vB.1 hvBcoeff vB.2 (by norm_num [agreements, n, errors])
      (by norm_num [agreements, n, errors])).2.2
  refine ⟨{
    QA := QA
    QB := QB
    QC := QC
    QA_ne_zero := hQA
    QB_ne_zero := hQB
    QC_ne_zero := hQC
    QA_mem := by
      simpa [Profile.weightedCap, profileA, agreements, n, errors, w] using hQAbox
    QB_mem := by
      simpa [Profile.weightedCap, profileB, agreements, n, errors, w] using hQBbox
    QC_mem := by
      simpa [Profile.weightedCap, profileC, profileA, agreements, n, errors, w, QC]
        using hQAbox
    gcd12_mem := by
      simpa [Profile.weightedCap, H, gcd12, profileA, agreements, n, errors, w]
        using hHbox1666
    oldCore_ys_le := by
      simpa [gcd123, gcd12, G, H, QC] using hGys
    oldCore_dvd_B := by
      intro v
      simpa [gcd123, gcd12, G, H, QC] using hGH.trans (hHdivB v)
    universal_cover := by
      intro gamma P support hP hcard hvalues
      apply recursive_branch_of_three_vanishings
      · dsimp only [QA]
        rw [kernelReconstructLinear_apply]
        exact hUnivA gamma P support hP hcard hvalues
      · dsimp only [QB]
        rw [kernelReconstructLinear_apply]
        exact hUnivB gamma P support hP hcard hvalues
      · dsimp only [QC, QA]
        rw [kernelReconstructLinear_apply]
        exact hUnivA gamma P support hP hcard hvalues
  }⟩

 

theorem exists_selected_interpolants (u0 u1 : I → K) :
    Nonempty (SelectedInterpolants6750Source u0 u1) := by
  apply exists_selected_interpolants_of_profileB_cap
  intro a0 a1 beta _ _ b
  exact profileB_commonGCD_total_le a0 a1 b

end

end ProximityPrize.SubmissionLower.ContactKernelSelectedInterpolation6750Research
