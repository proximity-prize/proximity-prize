import ProximityPrize.SubmissionLower.PackedLegacyCore2
import ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803

/-!
# Selected interpolation pair at agreement 181363

Only the two kernels used to choose the final pair are repeated here.  The
larger joined-kernel scaffolding in `LocatorSelection` is not needed by the
selection theorem itself.
-/

namespace ProximityPrize.SubmissionLower.LocatorSelection6803

open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137
  RCN183

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : StrongNormalizationMonoid P4 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid P4 :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

abbrev TCapKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 32826703 131071 6679 56 181
    IRSProfile.domain u0 u1

abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 20131293 131071 14261 34 111
    IRSProfile.domain u0 u1

theorem gateTCap : Fintype.card I * localRankBound 181 6679 56 <
    coefficientCount 32826703 131071 6679 56 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h : coefficientCount 32826703 131071 6679 56 -
      262144 * localRankBound 181 6679 56 = 367415844 := by
    simpa only [LocatorSelectionArithmetic6803.weightedTCap] using
      LocatorSelectionArithmetic6803.kernelTCap_nullity
  omega

theorem gateB : Fintype.card I * localRankBound 111 14261 34 <
    coefficientCount 20131293 131071 14261 34 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h : coefficientCount 20131293 131071 14261 34 -
      262144 * localRankBound 111 14261 34 = 9495675 := by
    simpa only [LocatorSelectionArithmetic6803.weightedB] using
      LocatorSelectionArithmetic6803.kernelB_nullity
  omega

private theorem gcd_mul_right_plain_associated
    (P H q : P4) (hc : IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd P (H * q) ∣ P := gcd_dvd_left P (H * q)
    have hright : gcd P (H * q) ∣ H * q := gcd_dvd_right P (H * q)
    have hcop : IsRelPrime (gcd P (H * q)) q :=
      hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))

private theorem gcd_mul_left_plain_associated
    (H q P : P4) (hc : IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd (H * q) P ∣ H * q := gcd_dvd_left (H * q) P
    have hright : gcd (H * q) P ∣ P := gcd_dvd_right (H * q) P
    have hcop : IsRelPrime (gcd (H * q) P) q :=
      hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)

structure SelectedPair (u0 u1 : I → K) where
  QA : P4
  QB : P4
  QA_ne : QA ≠ 0
  QB_ne : QB ≠ 0
  QA_flag : QA ∈ globalCoefficientBox K 32826703 131071 6679 56
  QB_flag : QB ∈ globalCoefficientBox K 20131293 131071 14261 34
  common_divides_TCap : ∀ v : TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 32826703 131071 6679 56 v.1
  common_divides_B : ∀ v : BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 20131293 131071 14261 34 v.1
  universal_vanishing :
    ∀ (gamma : K) (P : Polynomial K) (points : Finset I),
      P.natDegree ≤ 131071 → 181363 ≤ points.card →
      (∀ i ∈ points,
        P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA = 0 ∧
        RCN319.specialization K P gamma QB = 0

theorem exists_selected_pair (u0 u1 : I → K) :
    Nonempty (SelectedPair u0 u1) := by
  classical
  obtain ⟨thetaT, htT, hkT⟩ := exists_nonzero_kernel_array (I := I)
    K 32826703 131071 6679 56 181 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB, htB, hkB⟩ := exists_nonzero_kernel_array (I := I)
    K 20131293 131071 14261 34 111 IRSProfile.domain u0 u1 gateB
  let vT0 : TCapKernel u0 u1 :=
    ⟨thetaT, LinearMap.mem_ker.mpr hkT⟩
  let vB0 : BKernel u0 u1 :=
    ⟨thetaB, LinearMap.mem_ker.mpr hkB⟩
  letI : Nontrivial (TCapKernel u0 u1) := ⟨⟨vT0, 0, by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI : Nontrivial (BKernel u0 u1) := ⟨⟨vB0, 0, by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT := Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB := Module.Free.chooseBasis K (BKernel u0 u1)
  letI : Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Module.Finite.finite_basis bT
  letI : Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI : Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Fintype.ofFinite _
  letI : Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Fintype.ofFinite _
  letI : Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    bT.index_nonempty
  letI : Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    bB.index_nonempty
  let HT := commonGCD (TCapKernel u0 u1) bT
  let HB := commonGCD (BKernel u0 u1) bB
  have hHT : HT ≠ 0 := commonGCD_ne_zero (TCapKernel u0 u1) bT
  have hHB : HB ≠ 0 := commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox : HB ∈ globalCoefficientBox K 20131293 131071 14261 34 :=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB : (normalizedFactorSet HB).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 20131293 14261 34
      hHB hHBbox (by norm_num)
  obtain ⟨vA, hvA, hcopA⟩ := exists_common_quotient_isRelPrime
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA := commonQuotientLinear (TCapKernel u0 u1) bT hHT vA
  let QA := submoduleReconstructLinear (TCapKernel u0 u1) vA
  have hQAeq : QA = HT * qA := recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (TCapKernel u0 u1)) HT
    (commonDivisorProof (TCapKernel u0 u1) bT) vA
  have hQA : QA ≠ 0 := by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (TCapKernel u0 u1)
    simpa only [map_zero, QA] using hz
  have hQAbox : QA ∈ globalCoefficientBox K 32826703 131071 6679 56 := by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 32826703 131071 6679 56 vA.1
  have hcardQA : (normalizedFactorSet QA).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 32826703 6679 56
      hQA hQAbox (by norm_num)
  obtain ⟨vB, hvB, hcopB⟩ := exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB := commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB := submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq : QB = HB * qB := recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB : QB ≠ 0 := by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero, QB] using hz
  have hQBbox : QB ∈ globalCoefficientBox K 20131293 131071 14261 34 := by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 20131293 131071 14261 34 vB.1
  have hAssocA : Associated (gcd QA HB) (gcd HT HB) := by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HT qA HB hcopA
  have hAssocB : Associated (gcd QA QB) (gcd QA HB) := by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc := hAssocB.trans hAssocA
  have hHHT : gcd QA QB ∣ HT :=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB : gcd QA QB ∣ HB :=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA := QA, QB := QB, QA_ne := hQA, QB_ne := hQB,
    QA_flag := hQAbox, QB_flag := hQBbox,
    common_divides_TCap := ?_, common_divides_B := ?_,
    universal_vanishing := ?_ }⟩
  · intro v
    exact hHHT.trans (commonGCD_dvd (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        32826703 131071 6679 56 181 181363 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide) (by decide) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        20131293 131071 14261 34 111 181363 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide) (by decide) P gamma points hP hcard hvalues

end

end ProximityPrize.SubmissionLower.LocatorSelection6803
