import ProximityPrize.SubmissionLower.L4
import ProximityPrize.SubmissionLower.RegularColonArithmetic
namespace ProximityPrize.SubmissionLower.TwoKernelSelection
open ProximityPrize.Benchmark
open RCN100 RCN119
open RCN101 RCN180
open RCN181 RCN137
open RCN183
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : StrongNormalizationMonoid P4 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid P4 :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

/- Keep these divisibility arguments in the same plain-GCD instance as
   `SelectedPair`.  The similarly named L2 lemma is specialized to its local
   normalized GCD, so neither it nor normalized `gcd_comm` should be used here. -/
private theorem gcd_mul_right_plain_associated
    (P H q : P4) (hc : IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd P (H * q) ∣ P := gcd_dvd_left P (H * q)
    have hright : gcd P (H * q) ∣ H * q := gcd_dvd_right P (H * q)
    have hcop : IsRelPrime (gcd P (H * q)) q := hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))

private theorem gcd_mul_left_plain_associated
    (H q P : P4) (hc : IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P) := by
  apply associated_of_dvd_dvd
  · have hleft : gcd (H * q) P ∣ H * q := gcd_dvd_left (H * q) P
    have hright : gcd (H * q) P ∣ P := gcd_dvd_right (H * q) P
    have hcop : IsRelPrime (gcd (H * q) P) q := hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)

abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 7645344 131071 240000 12 42 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 14744592 131071 1283 25 81 IRSProfile.domain u0 u1

theorem gateA : Fintype.card I * localRankBound 42 240000 12 <
    coefficientCount 7645344 131071 240000 12 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := RegularColonArithmetic.kernelA_nullity
  omega
theorem gateB : Fintype.card I * localRankBound 81 1283 25 <
    coefficientCount 14744592 131071 1283 25 := by
  rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index]]
  have h := RegularColonArithmetic.kernelB_nullity
  omega

structure SelectedPair (u0 u1 : I → K) where
  QA : P4
  QB : P4
  QA_ne : QA ≠ 0
  QB_ne : QB ≠ 0
  QA_flag : QA ∈ globalCoefficientBox K 7645344 131071 240000 12
  QB_flag : QB ∈ globalCoefficientBox K 14744592 131071 1283 25
  common_divides_A : ∀ v : AKernel u0 u1,
    gcd QA QB ∣ reconstruct K 7645344 131071 240000 12 v.1
  common_divides_B : ∀ v : BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 14744592 131071 1283 25 v.1
  universal_vanishing :
    ∀ (gamma : K) (P : Polynomial K) (points : Finset I),
      P.natDegree ≤ 131071 → 182032 ≤ points.card →
      (∀ i ∈ points, P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA = 0 ∧
        RCN319.specialization K P gamma QB = 0

theorem exists_selected_pair (u0 u1 : I → K) : Nonempty (SelectedPair u0 u1) := by
  classical
  have hExistsA := exists_nonzero_kernel_array (I := I)
    K 7645344 131071 240000 12 42 IRSProfile.domain u0 u1 gateA
  obtain ⟨thetaA, htA, hkA⟩ := hExistsA
  have hExistsB := exists_nonzero_kernel_array (I := I)
    K 14744592 131071 1283 25 81 IRSProfile.domain u0 u1 gateB
  obtain ⟨thetaB, htB, hkB⟩ := hExistsB
  let vA0 : AKernel u0 u1 := ⟨thetaA, LinearMap.mem_ker.mpr hkA⟩
  let vB0 : BKernel u0 u1 := ⟨thetaB, LinearMap.mem_ker.mpr hkB⟩
  letI : Nontrivial (AKernel u0 u1) := ⟨⟨vA0, 0, by
    intro h
    exact htA (congrArg Subtype.val h)⟩⟩
  letI : Nontrivial (BKernel u0 u1) := ⟨⟨vB0, 0, by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bA := Module.Free.chooseBasis K (AKernel u0 u1)
  let bB := Module.Free.chooseBasis K (BKernel u0 u1)
  letI : Finite (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) :=
    Module.Finite.finite_basis bA
  letI : Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI : Fintype (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) := Fintype.ofFinite _
  letI : Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) := Fintype.ofFinite _
  letI : Nonempty (Module.Free.ChooseBasisIndex K (AKernel u0 u1)) := bA.index_nonempty
  letI : Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) := bB.index_nonempty
  let HA := commonGCD (AKernel u0 u1) bA
  let HB := commonGCD (BKernel u0 u1) bB
  have hHA : HA ≠ 0 := commonGCD_ne_zero (AKernel u0 u1) bA
  have hHB : HB ≠ 0 := commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox : HB ∈ globalCoefficientBox K 14744592 131071 1283 25 :=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB : (normalizedFactorSet HB).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 14744592 1283 25
      hHB hHBbox (by norm_num)
  obtain ⟨vA, hvA, hcopA⟩ := exists_common_quotient_isRelPrime
    (AKernel u0 u1) bA hHA HB hHB hcardHB
  let qA := commonQuotientLinear (AKernel u0 u1) bA hHA vA
  let QA := submoduleReconstructLinear (AKernel u0 u1) vA
  have hQAeq : QA = HA * qA := recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (AKernel u0 u1)) HA
    (commonDivisorProof (AKernel u0 u1) bA) vA
  have hQA : QA ≠ 0 := by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (AKernel u0 u1)
    simpa only [map_zero, QA] using hz
  have hQAbox : QA ∈ globalCoefficientBox K 7645344 131071 240000 12 := by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 7645344 131071 240000 12 vA.1
  have hcardQA : (normalizedFactorSet QA).card < ENat.card K :=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 7645344 240000 12
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
  have hQBbox : QB ∈ globalCoefficientBox K 14744592 131071 1283 25 := by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 14744592 131071 1283 25 vB.1
  have hAssocA : Associated (gcd QA HB) (gcd HA HB) := by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HA qA HB hcopA
  have hAssocB : Associated (gcd QA QB) (gcd QA HB) := by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc := hAssocB.trans hAssocA
  have hHHA : gcd QA QB ∣ HA :=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HA HB)
  have hHHB : gcd QA QB ∣ HB :=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HA HB)
  have hva : vA.1 ≠ 0 := by
    intro h
    exact hvA (Subtype.ext h)
  have hvb : vB.1 ≠ 0 := by
    intro h
    exact hvB (Subtype.ext h)
  have hUnivA := (nonzero_kernel_member_universal K
    7645344 131071 240000 12 42 182032 IRSProfile.domain u0 u1
    vA.1 hva vA.2 (by decide) (by decide)).2.2
  have hUnivB := (nonzero_kernel_member_universal K
    14744592 131071 1283 25 81 182032 IRSProfile.domain u0 u1
    vB.1 hvb vB.2 (by decide) (by decide)).2.2
  refine ⟨{
    QA := QA, QB := QB, QA_ne := hQA, QB_ne := hQB
    QA_flag := hQAbox, QB_flag := hQBbox
    common_divides_A := fun v => hHHA.trans (commonGCD_dvd (AKernel u0 u1) bA v)
    common_divides_B := fun v => hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
    universal_vanishing := ?_ }⟩
  intro gamma P points hP hcard hvalues
  constructor
  · dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact hUnivA gamma P points hP hcard hvalues
  · dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact hUnivB gamma P points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.TwoKernelSelection
