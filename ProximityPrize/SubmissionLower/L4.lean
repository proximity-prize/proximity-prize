import ProximityPrize.SubmissionLower.L2
namespace ProximityPrize.SubmissionLower.RCN183
open scoped BigOperators
open ProximityPrize.Benchmark
open RCN100 RCN119
open RCN101
open RCN180 RCN181
open RCN137 RCN130
open RCN234
open RCN156
open RCN081
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field
local instance : StrongNormalizationMonoid GlobalPoly :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance : NormalizedGCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
def agreements6733 : ℕ := 182042
abbrev AKernel (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K := IRSProfile.Field)
   7645764 131071 84439 12 42 IRSProfile.domain u₀ u₁
abbrev BKernel (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K := IRSProfile.Field)
   14745402 131071 1262 25 81 IRSProfile.domain u₀ u₁
abbrev CKernel (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K := IRSProfile.Field)
   7463722 131071 41787 12 41 IRSProfile.domain u₀ u₁
theorem gateA :
   Fintype.card IRSProfile.Index * localRankBound 42 84439 12 <
     coefficientCount 7645764 131071 84439 12 := by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7645764 131071 84439 12 59 (by decide) (by decide)]
 decide
theorem gateB :
   Fintype.card IRSProfile.Index * localRankBound 81 1262 25 <
     coefficientCount 14745402 131071 1262 25 := by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   14745402 131071 1262 25 113 (by decide) (by decide)]
 decide
theorem gateC :
   Fintype.card IRSProfile.Index * localRankBound 41 41787 12 <
     coefficientCount 7463722 131071 41787 12 := by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7463722 131071 41787 12 57 (by decide) (by decide)]
 decide
theorem field_cardinality :
   Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 := by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem normalizedFactorSet_card_lt_field_of_mem_flagBox
   (P : GlobalPoly) (D L s : ℕ) (hP : P ≠ 0)
   (hbox : P ∈ globalCoefficientBox IRSProfile.Field D 131071 L s)
   (hsmall : (D - 1) + (D - 1) / 131071 + s + L <
     (2130706433 : ℕ) ^ 6) :
   (normalizedFactorSet P).card < ENat.card IRSProfile.Field := by
 have hle := normalizedFactorSet_card_le_of_mem_flagBox
   P D 131071 L s (by decide) hP hbox
 rw [ENat.card_eq_coe_fintype_card,field_cardinality]
 exact_mod_cast hle.trans_lt hsmall
theorem commonGCD_mem_flagBox
   {D L s : ℕ}
   (V : Submodule IRSProfile.Field (CoefficientIndex D 131071 L s → IRSProfile.Field))
   {ι : Type*} [Fintype ι] [Nonempty ι]
   (b : Module.Basis ι IRSProfile.Field V) :
   commonGCD V b ∈ globalCoefficientBox IRSProfile.Field D 131071 L s := by
 let i : ι := Classical.choice inferInstance
 let Q := reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQ : Q ≠ 0 := by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hb
   apply b.ne_zero i
   exact Subtype.ext hb
 exact mem_flagGlobalCoefficientBox_of_dvd (commonGCD V b) Q
   D 131071 L s hQ (commonGCD_dvd_basis V b i)
   (reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1)
local instance : GCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
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
private theorem gcd_mul_left_plain_associated
   (H q P : GlobalPoly) (hc : IsRelPrime q P) :
   Associated (gcd (H * q) P) (gcd H P) := by
 apply associated_of_dvd_dvd
 · have hleft : gcd (H * q) P ∣ H * q := gcd_dvd_left (H * q) P
   have hright : gcd (H * q) P ∣ P := gcd_dvd_right (H * q) P
   have hcop : IsRelPrime (gcd (H * q) P) q :=
     hc.symm.of_dvd_left hright
   exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
 · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
     (gcd_dvd_right H P)
@[simp] theorem submoduleReconstructLinear_apply
   {D L s : ℕ}
   (V : Submodule IRSProfile.Field
     (CoefficientIndex D 131071 L s → IRSProfile.Field)) (v : V) :
   submoduleReconstructLinear V v =
     reconstruct IRSProfile.Field D 131071 L s v.1 := rfl
structure SelectedInterpolants
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) where
 QA : GlobalPoly
 QB : GlobalPoly
 QC : GlobalPoly
 H : GlobalPoly
 G : GlobalPoly
 H_eq : H = gcd QA QB
 G_eq : G = gcd H QC
 QA_ne : QA ≠ 0
 QB_ne : QB ≠ 0
 QC_ne : QC ≠ 0
 H_ne : H ≠ 0
 G_ne : G ≠ 0
 QA_flag : QA ∈ globalCoefficientBox IRSProfile.Field
   7645764 131071 84439 12
 QB_flag : QB ∈ globalCoefficientBox IRSProfile.Field
   14745402 131071 1262 25
 QC_flag : QC ∈ globalCoefficientBox IRSProfile.Field
   7463722 131071 41787 12
 QA_ordinary : QA ∈ RCN174.globalCoefficientBox IRSProfile.Field
   7645764 131071 84439 12
 QB_ordinary : QB ∈ RCN174.globalCoefficientBox IRSProfile.Field
   14745402 131071 1262 25
 QC_ordinary : QC ∈ RCN174.globalCoefficientBox IRSProfile.Field
   7463722 131071 41787 12
 H_flagA : H ∈ globalCoefficientBox IRSProfile.Field
   7645764 131071 84439 12
 H_flagB : H ∈ globalCoefficientBox IRSProfile.Field
   14745402 131071 1262 25
 G_flagA : G ∈ globalCoefficientBox IRSProfile.Field
   7645764 131071 84439 12
 G_flagB : G ∈ globalCoefficientBox IRSProfile.Field
   14745402 131071 1262 25
 G_flagC : G ∈ globalCoefficientBox IRSProfile.Field
   7463722 131071 41787 12
 H_dvd_A : ∀ v : AKernel u₀ u₁,
   H ∣ reconstruct IRSProfile.Field 7645764 131071 84439 12 v.1
 H_dvd_B : ∀ v : BKernel u₀ u₁,
   H ∣ reconstruct IRSProfile.Field 14745402 131071 1262 25 v.1
 G_dvd_A : ∀ v : AKernel u₀ u₁,
   G ∣ reconstruct IRSProfile.Field 7645764 131071 84439 12 v.1
 G_dvd_B : ∀ v : BKernel u₀ u₁,
   G ∣ reconstruct IRSProfile.Field 14745402 131071 1262 25 v.1
 G_dvd_C : ∀ v : CKernel u₀ u₁,
   G ∣ reconstruct IRSProfile.Field 7463722 131071 41787 12 v.1
 H_ys_le : wt residualYSWeights H ≤ 55
 H_total_le : wt residualTotalWeights H ≤ 1261
 G_ys_le : wt residualYSWeights G ≤ 55
 G_total_le : wt residualTotalWeights G ≤ 1261
 G_corner : wt residualYSWeights G ≤ 54 ∨
   wt residualSWeights G ≤ 11
 universal_vanishing :
   ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
     (support : Finset IRSProfile.Index),
     P.natDegree ≤ 131071 → agreements6733 ≤ support.card →
     (∀ i ∈ support,
       P.eval (IRSProfile.domain i) = u₀ i + gamma * u₁ i) →
     RCN122.specialization
         IRSProfile.Field P gamma QA = 0 ∧
       RCN122.specialization
         IRSProfile.Field P gamma QB = 0 ∧
     RCN122.specialization
         IRSProfile.Field P gamma QC = 0
namespace SelectedInterpolants
variable {u₀ u₁ : IRSProfile.Index → IRSProfile.Field}
theorem H_ordinaryA (S : SelectedInterpolants u₀ u₁) :
   S.H ∈ RCN174.globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 :=
 flag_box_to_ordinary IRSProfile.Field
   7645764 131071 84439 12 S.H S.H_flagA
theorem H_ordinaryB (S : SelectedInterpolants u₀ u₁) :
   S.H ∈ RCN174.globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 :=
 flag_box_to_ordinary IRSProfile.Field
   14745402 131071 1262 25 S.H S.H_flagB
theorem G_ordinaryA (S : SelectedInterpolants u₀ u₁) :
   S.G ∈ RCN174.globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 :=
 flag_box_to_ordinary IRSProfile.Field
   7645764 131071 84439 12 S.G S.G_flagA
theorem G_ordinaryB (S : SelectedInterpolants u₀ u₁) :
   S.G ∈ RCN174.globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 :=
 flag_box_to_ordinary IRSProfile.Field
   14745402 131071 1262 25 S.G S.G_flagB
theorem G_ordinaryC (S : SelectedInterpolants u₀ u₁) :
   S.G ∈ RCN174.globalCoefficientBox IRSProfile.Field
     7463722 131071 41787 12 :=
 flag_box_to_ordinary IRSProfile.Field
   7463722 131071 41787 12 S.G S.G_flagC
theorem H_dvd_A_commonGCD (S : SelectedInterpolants u₀ u₁)
   {ι : Type*} [Fintype ι]
   (b : Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   S.H ∣ commonGCD (AKernel u₀ u₁) b :=
 (dvd_commonGCD_iff (AKernel u₀ u₁) b S.H).2 S.H_dvd_A
theorem H_dvd_B_commonGCD (S : SelectedInterpolants u₀ u₁)
   {ι : Type*} [Fintype ι]
   (b : Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   S.H ∣ commonGCD (BKernel u₀ u₁) b :=
 (dvd_commonGCD_iff (BKernel u₀ u₁) b S.H).2 S.H_dvd_B
theorem G_dvd_A_commonGCD (S : SelectedInterpolants u₀ u₁)
   {ι : Type*} [Fintype ι]
   (b : Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   S.G ∣ commonGCD (AKernel u₀ u₁) b :=
 (dvd_commonGCD_iff (AKernel u₀ u₁) b S.G).2 S.G_dvd_A
theorem G_dvd_B_commonGCD (S : SelectedInterpolants u₀ u₁)
   {ι : Type*} [Fintype ι]
   (b : Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   S.G ∣ commonGCD (BKernel u₀ u₁) b :=
 (dvd_commonGCD_iff (BKernel u₀ u₁) b S.G).2 S.G_dvd_B
theorem G_dvd_C_commonGCD (S : SelectedInterpolants u₀ u₁)
   {ι : Type*} [Fintype ι]
   (b : Module.Basis ι IRSProfile.Field (CKernel u₀ u₁)) :
   S.G ∣ commonGCD (CKernel u₀ u₁) b :=
 (dvd_commonGCD_iff (CKernel u₀ u₁) b S.G).2 S.G_dvd_C
end SelectedInterpolants
theorem exists_selected_interpolants
   (u₀ u₁ : IRSProfile.Index → IRSProfile.Field) :
   Nonempty (SelectedInterpolants u₀ u₁) := by
 classical
 obtain ⟨thetaA,hthetaA,hkernelA⟩ := exists_nonzero_kernel_array
   IRSProfile.Field 7645764 131071 84439 12 42
     IRSProfile.domain u₀ u₁ gateA
 obtain ⟨thetaB,hthetaB,hkernelB⟩ := exists_nonzero_kernel_array
   IRSProfile.Field 14745402 131071 1262 25 81
     IRSProfile.domain u₀ u₁ gateB
 obtain ⟨thetaC,hthetaC,hkernelC⟩ := exists_nonzero_kernel_array
   IRSProfile.Field 7463722 131071 41787 12 41
     IRSProfile.domain u₀ u₁ gateC
 let vA0 : AKernel u₀ u₁ := ⟨thetaA,LinearMap.mem_ker.mpr hkernelA⟩
 let vB0 : BKernel u₀ u₁ := ⟨thetaB,LinearMap.mem_ker.mpr hkernelB⟩
 let vC0 : CKernel u₀ u₁ := ⟨thetaC,LinearMap.mem_ker.mpr hkernelC⟩
 letI : Nontrivial (AKernel u₀ u₁) := ⟨⟨vA0,0,by
   intro h
   apply hthetaA
   exact congrArg Subtype.val h⟩⟩
 letI : Nontrivial (BKernel u₀ u₁) := ⟨⟨vB0,0,by
   intro h
   apply hthetaB
   exact congrArg Subtype.val h⟩⟩
 letI : Nontrivial (CKernel u₀ u₁) := ⟨⟨vC0,0,by
   intro h
   apply hthetaC
   exact congrArg Subtype.val h⟩⟩
 let bA := Module.Free.chooseBasis IRSProfile.Field (AKernel u₀ u₁)
 let bB := Module.Free.chooseBasis IRSProfile.Field (BKernel u₀ u₁)
 let bC := Module.Free.chooseBasis IRSProfile.Field (CKernel u₀ u₁)
 letI : Finite (Module.Free.ChooseBasisIndex IRSProfile.Field (AKernel u₀ u₁)) :=
   Module.Finite.finite_basis bA
 letI : Finite (Module.Free.ChooseBasisIndex IRSProfile.Field (BKernel u₀ u₁)) :=
   Module.Finite.finite_basis bB
 letI : Finite (Module.Free.ChooseBasisIndex IRSProfile.Field (CKernel u₀ u₁)) :=
   Module.Finite.finite_basis bC
 letI : Fintype (Module.Free.ChooseBasisIndex IRSProfile.Field (AKernel u₀ u₁)) :=
   Fintype.ofFinite _
 letI : Fintype (Module.Free.ChooseBasisIndex IRSProfile.Field (BKernel u₀ u₁)) :=
   Fintype.ofFinite _
 letI : Fintype (Module.Free.ChooseBasisIndex IRSProfile.Field (CKernel u₀ u₁)) :=
   Fintype.ofFinite _
 letI : Nonempty (Module.Free.ChooseBasisIndex IRSProfile.Field (AKernel u₀ u₁)) :=
   bA.index_nonempty
 letI : Nonempty (Module.Free.ChooseBasisIndex IRSProfile.Field (BKernel u₀ u₁)) :=
   bB.index_nonempty
 letI : Nonempty (Module.Free.ChooseBasisIndex IRSProfile.Field (CKernel u₀ u₁)) :=
   bC.index_nonempty
 let HA := commonGCD (AKernel u₀ u₁) bA
 let HB := commonGCD (BKernel u₀ u₁) bB
 let HC := commonGCD (CKernel u₀ u₁) bC
 have hHA : HA ≠ 0 := by
   dsimp [HA]
   exact commonGCD_ne_zero (AKernel u₀ u₁) bA
 have hHB : HB ≠ 0 := by
   dsimp [HB]
   exact commonGCD_ne_zero (BKernel u₀ u₁) bB
 have hHC : HC ≠ 0 := by
   dsimp [HC]
   exact commonGCD_ne_zero (CKernel u₀ u₁) bC
 have hHAbox : HA ∈ globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 := by
   dsimp [HA]
   exact commonGCD_mem_flagBox (AKernel u₀ u₁) bA
 have hHBbox : HB ∈ globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 := by
   dsimp [HB]
   exact commonGCD_mem_flagBox (BKernel u₀ u₁) bB
 have hHCbox : HC ∈ globalCoefficientBox IRSProfile.Field
     7463722 131071 41787 12 := by
   dsimp [HC]
   exact commonGCD_mem_flagBox (CKernel u₀ u₁) bC
 have hcardHB : (normalizedFactorSet HB).card < ENat.card IRSProfile.Field :=
   normalizedFactorSet_card_lt_field_of_mem_flagBox HB 14745402 1262 25
     hHB hHBbox (by norm_num)
 obtain ⟨vA,hvA,hcopA⟩ := exists_common_quotient_isRelPrime
   (AKernel u₀ u₁) bA hHA HB hHB hcardHB
 let qA := commonQuotientLinear (AKernel u₀ u₁) bA hHA vA
 let QA := submoduleReconstructLinear (AKernel u₀ u₁) vA
 have hQAeq : QA = HA * qA := by
   exact recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear (AKernel u₀ u₁)) HA
     (commonDivisorProof (AKernel u₀ u₁) bA) vA
 have hQA : QA ≠ 0 := by
   intro hz
   apply hvA
   apply submoduleReconstructLinear_injective (AKernel u₀ u₁)
   simpa only [map_zero,QA] using hz
 have hQAbox : QA ∈ globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 := by
   dsimp only [QA]
   rw [submoduleReconstructLinear_apply]
   exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 vA.1
 have hcardQA : (normalizedFactorSet QA).card < ENat.card IRSProfile.Field :=
   normalizedFactorSet_card_lt_field_of_mem_flagBox QA 7645764 84439 12
     hQA hQAbox (by norm_num)
 obtain ⟨vB,hvB,hcopB⟩ := exists_common_quotient_isRelPrime
   (BKernel u₀ u₁) bB hHB QA hQA hcardQA
 let qB := commonQuotientLinear (BKernel u₀ u₁) bB hHB vB
 let QB := submoduleReconstructLinear (BKernel u₀ u₁) vB
 have hQBeq : QB = HB * qB := by
   exact recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear (BKernel u₀ u₁)) HB
     (commonDivisorProof (BKernel u₀ u₁) bB) vB
 have hQB : QB ≠ 0 := by
   intro hz
   apply hvB
   apply submoduleReconstructLinear_injective (BKernel u₀ u₁)
   simpa only [map_zero,QB] using hz
 have hQBbox : QB ∈ globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 := by
   dsimp only [QB]
   rw [submoduleReconstructLinear_apply]
   exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 vB.1
 have hAssocA : Associated (gcd QA HB) (gcd HA HB) := by
   have h := gcd_mul_left_plain_associated HA qA HB
     (by simpa only [qA] using hcopA)
   rwa [← hQAeq] at h
 have hAssocB : Associated (gcd QA QB) (gcd QA HB) := by
   have h := gcd_mul_right_plain_associated QA HB qB
     (by simpa only [qB] using hcopB)
   rwa [← hQBeq] at h
 let H := gcd QA QB
 have hAssocH : Associated H (gcd HA HB) := by
   exact hAssocB.trans hAssocA
 have hH : H ≠ 0 := by
   intro hz
   have hz' : gcd QA QB = 0 := by simpa only [H] using hz
   exact hQA ((gcd_eq_zero_iff QA QB).mp hz').1
 have hHHA : H ∣ HA :=
   hAssocH.dvd_iff_dvd_left.mpr (gcd_dvd_left HA HB)
 have hHHB : H ∣ HB :=
   hAssocH.dvd_iff_dvd_left.mpr (gcd_dvd_right HA HB)
 have hHdivA : ∀ v : AKernel u₀ u₁,
     H ∣ reconstruct IRSProfile.Field 7645764 131071 84439 12 v.1 := by
   intro v
   exact hHHA.trans (commonGCD_dvd (AKernel u₀ u₁) bA v)
 have hHdivB : ∀ v : BKernel u₀ u₁,
     H ∣ reconstruct IRSProfile.Field 14745402 131071 1262 25 v.1 := by
   intro v
   exact hHHB.trans (commonGCD_dvd (BKernel u₀ u₁) bB v)
 have hHboxA : H ∈ globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 :=
   mem_flagGlobalCoefficientBox_of_dvd H QA 7645764 131071 84439 12
     hQA (by dsimp only [H]; exact gcd_dvd_left QA QB) hQAbox
 have hHboxB : H ∈ globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 :=
   mem_flagGlobalCoefficientBox_of_dvd H QB 14745402 131071 1262 25
     hQB (by dsimp only [H]; exact gcd_dvd_right QA QB) hQBbox
 have hcardH : (normalizedFactorSet H).card < ENat.card IRSProfile.Field :=
   normalizedFactorSet_card_lt_field_of_mem_flagBox H 7645764 84439 12
     hH hHboxA (by norm_num)
 obtain ⟨vC,hvC,hcopC⟩ := exists_common_quotient_isRelPrime
   (CKernel u₀ u₁) bC hHC H hH hcardH
 let qC := commonQuotientLinear (CKernel u₀ u₁) bC hHC vC
 let QC := submoduleReconstructLinear (CKernel u₀ u₁) vC
 have hQCeq : QC = HC * qC := by
   exact recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear (CKernel u₀ u₁)) HC
     (commonDivisorProof (CKernel u₀ u₁) bC) vC
 have hQC : QC ≠ 0 := by
   intro hz
   apply hvC
   apply submoduleReconstructLinear_injective (CKernel u₀ u₁)
   simpa only [map_zero,QC] using hz
 have hQCbox : QC ∈ globalCoefficientBox IRSProfile.Field
     7463722 131071 41787 12 := by
   dsimp only [QC]
   rw [submoduleReconstructLinear_apply]
   exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
     7463722 131071 41787 12 vC.1
 have hAssocG : Associated (gcd H QC) (gcd H HC) := by
   have h := gcd_mul_right_plain_associated H HC qC
     (by simpa only [qC] using hcopC)
   rwa [← hQCeq] at h
 let G := gcd H QC
 have hG : G ≠ 0 := by
   intro hz
   have hz' : gcd H QC = 0 := by simpa only [G] using hz
   exact hH ((gcd_eq_zero_iff H QC).mp hz').1
 have hGH : G ∣ H := by
   dsimp only [G]
   exact gcd_dvd_left H QC
 have hGHC : G ∣ HC := by
   apply hAssocG.dvd_iff_dvd_left.mpr
   exact gcd_dvd_right H HC
 have hGdivA : ∀ v : AKernel u₀ u₁,
     G ∣ reconstruct IRSProfile.Field 7645764 131071 84439 12 v.1 := by
   intro v
   exact hGH.trans (hHdivA v)
 have hGdivB : ∀ v : BKernel u₀ u₁,
     G ∣ reconstruct IRSProfile.Field 14745402 131071 1262 25 v.1 := by
   intro v
   exact hGH.trans (hHdivB v)
 have hGdivC : ∀ v : CKernel u₀ u₁,
     G ∣ reconstruct IRSProfile.Field 7463722 131071 41787 12 v.1 := by
   intro v
   exact hGHC.trans (commonGCD_dvd (CKernel u₀ u₁) bC v)
 have hGboxA : G ∈ globalCoefficientBox IRSProfile.Field
     7645764 131071 84439 12 :=
   mem_flagGlobalCoefficientBox_of_dvd G H 7645764 131071 84439 12
     hH hGH hHboxA
 have hGboxB : G ∈ globalCoefficientBox IRSProfile.Field
     14745402 131071 1262 25 :=
   mem_flagGlobalCoefficientBox_of_dvd G H 14745402 131071 1262 25
     hH hGH hHboxB
 have hGboxC : G ∈ globalCoefficientBox IRSProfile.Field
     7463722 131071 41787 12 :=
   mem_flagGlobalCoefficientBox_of_dvd G QC 7463722 131071 41787 12
     hQC (by dsimp only [G]; exact gcd_dvd_right H QC) hQCbox
 have hHAys : wt residualYSWeights HA ≤ 55 := by
   dsimp only [HA]
   exact RCN180.Caps6734.profileA_commonGCD_ys_le
     u₀ u₁ bA
 have hHAcorner : wt residualYSWeights HA ≤ 54 ∨
     wt residualSWeights HA ≤ 11 := by
   dsimp only [HA]
   exact RCN180.Caps6734.profileA_commonGCD_corner
     u₀ u₁ bA
 have hHBtotal : wt residualTotalWeights HB ≤ 1261 := by
   dsimp only [HB]
   exact RCN180.Caps6734.profileB_commonGCD_total_le
     u₀ u₁ bB
 have hHys : wt residualYSWeights H ≤ 55 :=
   (weightedTotalDegree_le_of_dvd residualYSWeights H HA hHHA hHA).trans hHAys
 have hHtotal : wt residualTotalWeights H ≤ 1261 :=
   (weightedTotalDegree_le_of_dvd residualTotalWeights H HB hHHB hHB).trans hHBtotal
 have hGys : wt residualYSWeights G ≤ 55 :=
   (weightedTotalDegree_le_of_dvd residualYSWeights G HA
     (hGH.trans hHHA) hHA).trans hHAys
 have hGtotal : wt residualTotalWeights G ≤ 1261 :=
   (weightedTotalDegree_le_of_dvd residualTotalWeights G HB
     (hGH.trans hHHB) hHB).trans hHBtotal
 have hGcorner : wt residualYSWeights G ≤ 54 ∨
     wt residualSWeights G ≤ 11 := by
   rcases hHAcorner with hys | hslope
   · exact Or.inl ((weightedTotalDegree_le_of_dvd residualYSWeights G HA
       (hGH.trans hHHA) hHA).trans hys)
   · exact Or.inr ((weightedTotalDegree_le_of_dvd residualSWeights G HA
       (hGH.trans hHHA) hHA).trans hslope)
 have hvAcoeff : vA.1 ≠ 0 := by
   intro hz
   apply hvA
   exact Subtype.ext hz
 have hvBcoeff : vB.1 ≠ 0 := by
   intro hz
   apply hvB
   exact Subtype.ext hz
 have hvCcoeff : vC.1 ≠ 0 := by
   intro hz
   apply hvC
   exact Subtype.ext hz
 have hUnivA := (nonzero_kernel_member_universal IRSProfile.Field
   7645764 131071 84439 12 42 agreements6733 IRSProfile.domain u₀ u₁
   vA.1 hvAcoeff vA.2 (by decide) (by norm_num [agreements6733])).2.2
 have hUnivB := (nonzero_kernel_member_universal IRSProfile.Field
   14745402 131071 1262 25 81 agreements6733 IRSProfile.domain u₀ u₁
   vB.1 hvBcoeff vB.2 (by decide) (by norm_num [agreements6733])).2.2
 have hUnivC := (nonzero_kernel_member_universal IRSProfile.Field
   7463722 131071 41787 12 41 agreements6733 IRSProfile.domain u₀ u₁
   vC.1 hvCcoeff vC.2 (by decide) (by norm_num [agreements6733])).2.2
 refine ⟨{
   QA := QA
   QB := QB
   QC := QC
   H := H
   G := G
   H_eq := rfl
   G_eq := rfl
   QA_ne := hQA
   QB_ne := hQB
   QC_ne := hQC
   H_ne := hH
   G_ne := hG
   QA_flag := hQAbox
   QB_flag := hQBbox
   QC_flag := hQCbox
   QA_ordinary := flag_box_to_ordinary IRSProfile.Field
     7645764 131071 84439 12 QA hQAbox
   QB_ordinary := flag_box_to_ordinary IRSProfile.Field
     14745402 131071 1262 25 QB hQBbox
   QC_ordinary := flag_box_to_ordinary IRSProfile.Field
     7463722 131071 41787 12 QC hQCbox
   H_flagA := hHboxA
   H_flagB := hHboxB
   G_flagA := hGboxA
   G_flagB := hGboxB
   G_flagC := hGboxC
   H_dvd_A := hHdivA
   H_dvd_B := hHdivB
   G_dvd_A := hGdivA
   G_dvd_B := hGdivB
   G_dvd_C := hGdivC
   H_ys_le := hHys
   H_total_le := hHtotal
   G_ys_le := hGys
   G_total_le := hGtotal
   G_corner := hGcorner
   universal_vanishing := by
     intro gamma P support hP hcard hvalues
     refine ⟨?_,?_,?_⟩
     · dsimp only [QA]
       rw [submoduleReconstructLinear_apply]
       exact hUnivA gamma P support hP hcard hvalues
     · dsimp only [QB]
       rw [submoduleReconstructLinear_apply]
       exact hUnivB gamma P support hP hcard hvalues
     · dsimp only [QC]
       rw [submoduleReconstructLinear_apply]
       exact hUnivC gamma P support hP hcard hvalues
 }⟩
end
end ProximityPrize.SubmissionLower.RCN183
