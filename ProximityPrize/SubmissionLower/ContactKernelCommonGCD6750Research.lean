import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

 









namespace ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactFlagRankKernel6641Research
open ContactFlagInterpolation6641Research
open ContactFlagKernelZeroExtension6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactFactorCaps
open ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

universe u v w

variable {K : Type u} [Field K]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

theorem flagReconstructLinear_injective (D w0 L s : Nat) :
    Function.Injective (flagReconstructLinear (K := K) D w0 L s) :=
  reconstruct_injective K D w0 L s

def flagReconstructBoxEquiv (D w0 L s : Nat) :
    (CoefficientIndex D w0 L s → K) ≃ₗ[K]
      globalCoefficientBox K D w0 L s :=
  LinearEquiv.ofBijective (flagReconstructIntoBox (K := K) D w0 L s) ⟨by
    intro theta eta h
    apply reconstruct_injective K D w0 L s
    exact congrArg Subtype.val h, by
    intro Q
    refine ⟨encodeFlagBox Q, ?_⟩
    apply Subtype.ext
    exact reconstruct_encodeFlagBox Q⟩

instance globalCoefficientBoxFinite (D w0 L s : Nat) :
    Module.Finite K (globalCoefficientBox K D w0 L s) :=
  Module.Finite.of_surjective (flagReconstructIntoBox (K := K) D w0 L s)
    (flagReconstructBoxEquiv (K := K) D w0 L s).surjective

theorem globalCoefficientBox_finrank (D w0 L s : Nat) :
    Module.finrank K (globalCoefficientBox K D w0 L s) =
      coefficientCount D w0 L s := by
  rw [← coefficient_index_card D w0 L s,
    ← Module.finrank_fintype_fun_eq_card K]
  exact LinearEquiv.finrank_eq
    (flagReconstructBoxEquiv (K := K) D w0 L s).symm

theorem mem_flagGlobalCoefficientBox_iff (Q : Poly4 K)
    (D w0 L s : Nat) (hD : 0 < D) :
    Q ∈ globalCoefficientBox K D w0 L s ↔
      wt residualTotalWeights Q ≤ L ∧
      wt residualSWeights Q ≤ s ∧
      wt (contactWeights w0) Q ≤ D - 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (weightedTotalDegree_le_iff residualTotalWeights Q L).mpr
      intro d hd
      have hq := h hd
      rw [weight_fin4]
      simp [residualTotalWeights]
      exact hq.1
    · apply (weightedTotalDegree_le_iff residualSWeights Q s).mpr
      intro d hd
      have hq := h hd
      rw [weight_fin4]
      simp [residualSWeights]
      exact hq.2.1
    · apply (weightedTotalDegree_le_iff (contactWeights w0) Q (D - 1)).mpr
      intro d hd
      rw [contact_weight]
      have hq := (h hd).2.2
      omega
  · rintro ⟨ht, hs, hc⟩ d hd
    have hdt :=
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
    have hds :=
      (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
    have hdc :=
      (MvPolynomial.le_weightedTotalDegree (contactWeights w0) hd).trans hc
    rw [weight_fin4] at hdt hds
    rw [contact_weight] at hdc
    simp [residualTotalWeights] at hdt
    simp [residualSWeights] at hds
    exact ⟨hdt, hds, by omega⟩

theorem residualYS_mul_le_contact_add_slope (Q : Poly4 K)
    (w0 : Nat) (hw : 1 ≤ w0) :
    w0 * wt residualYSWeights Q ≤
      wt (contactWeights w0) Q + wt residualSWeights Q := by
  by_cases hQ : Q = 0
  · subst Q
    simp [wt, MvPolynomial.weightedTotalDegree]
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup Q.support
    (MvPolynomial.support_nonempty.mpr hQ)
    (Finsupp.weight residualYSWeights)
  have hc := MvPolynomial.le_weightedTotalDegree (contactWeights w0) hd
  have hs := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  change wt residualYSWeights Q = Finsupp.weight residualYSWeights d at heq
  rw [weight_fin4] at heq hs
  rw [contact_weight] at hc
  simp [residualYSWeights] at heq
  simp [residualSWeights] at hs
  simp only [residualYSWeights, residualSWeights]
  rw [heq]
  have hwsub : w0 - 1 + 1 = w0 := by omega
  have hwmul : w0 * d 2 = (w0 - 1) * d 2 + d 2 := by
    calc
      w0 * d 2 = ((w0 - 1) + 1) * d 2 := by rw [hwsub]
      _ = (w0 - 1) * d 2 + d 2 := by ring
  calc
    w0 * (d 1 + d 2) ≤
        (d 0 + w0 * d 1 + (w0 - 1) * d 2) + d 2 := by
      rw [Nat.mul_add, hwmul]
      omega
    _ ≤ wt (contactWeights w0) Q + wt residualSWeights Q :=
      Nat.add_le_add hc hs

theorem quotient_mem_flagGlobalCoefficientBox_of_mul_eq
    (Q H R : Poly4 K) (D w0 L s contactLower totalLower slopeLower : Nat)
    (hQ : Q ≠ 0) (hH : H ≠ 0) (hR : R ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w0 L s)
    (heq : Q = H * R)
    (hcontact : contactLower ≤ wt (contactWeights w0) H)
    (htotal : totalLower ≤ wt residualTotalWeights H)
    (hslope : slopeLower ≤ wt residualSWeights H) :
    R ∈ globalCoefficientBox K (D - contactLower) w0
      (L - totalLower) (s - slopeLower) := by
  have hD : 0 < D := by
    rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d, hd⟩
    have := (hbox hd).2.2
    omega
  have hc := (mem_flagGlobalCoefficientBox_iff Q D w0 L s hD).mp hbox
  simp only [wt] at hc hcontact htotal hslope
  have hmulT := weightedTotalDegree_mul residualTotalWeights H R hH hR
  have hmulS := weightedTotalDegree_mul residualSWeights H R hH hR
  have hmulC := weightedTotalDegree_mul (contactWeights w0) H R hH hR
  rw [← heq] at hmulT hmulS hmulC
  have hDq : 0 < D - contactLower := by omega
  apply (mem_flagGlobalCoefficientBox_iff R (D - contactLower) w0
    (L - totalLower) (s - slopeLower) hDq).mpr
  simp only [wt]
  omega

theorem mem_flagGlobalCoefficientBox_of_dvd
    (F Q : Poly4 K) (D w0 L s : Nat)
    (hQ : Q ≠ 0) (hdiv : F ∣ Q)
    (hbox : Q ∈ globalCoefficientBox K D w0 L s) :
    F ∈ globalCoefficientBox K D w0 L s := by
  have hD : 0 < D := by
    rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d, hd⟩
    have := (hbox hd).2.2
    omega
  have hc := (mem_flagGlobalCoefficientBox_iff Q D w0 L s hD).mp hbox
  apply (mem_flagGlobalCoefficientBox_iff F D w0 L s hD).mpr
  exact ⟨
    (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans hc.1,
    (weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans hc.2.1,
    (weightedTotalDegree_le_of_dvd (contactWeights w0) F Q hdiv hQ).trans
      hc.2.2⟩

abbrev ConstraintKernel {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K) :=
  LinearMap.ker (constraintMap K D w0 L s m nodes u0 u1)

def kernelReconstructLinear {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K) :
    ConstraintKernel (K := K) D w0 L s m nodes u0 u1 →ₗ[K] Poly4 K :=
  (flagReconstructLinear (K := K) D w0 L s).comp
    (LinearMap.ker (constraintMap K D w0 L s m nodes u0 u1)).subtype

@[simp] theorem kernelReconstructLinear_apply {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    (z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1) :
    kernelReconstructLinear D w0 L s m nodes u0 u1 z =
      reconstruct K D w0 L s z.1 := rfl

theorem kernelReconstructLinear_injective {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K) :
    Function.Injective
      (kernelReconstructLinear (K := K) D w0 L s m nodes u0 u1) := by
  intro x y h
  apply Subtype.ext
  exact reconstruct_injective K D w0 L s h

def commonDivisorProof {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1)) :
    ∀ z, commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ∣
        kernelReconstructLinear D w0 L s m nodes u0 u1 z := by
  intro z
  rw [kernelReconstructLinear_apply]
  exact commonGCDAtMax_dvd _ b z

def commonQuotientLinear {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0) :
    ConstraintKernel (K := K) D w0 L s m nodes u0 u1 →ₗ[K] Poly4 K :=
  mappedFixedFactorQuotientLinearMap
    (commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b)
    hH (kernelReconstructLinear D w0 L s m nodes u0 u1)
    (commonDivisorProof D w0 L s m nodes u0 u1 b)

theorem mul_commonQuotientLinear {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (z : ConstraintKernel (K := K) D w0 L s m nodes u0 u1) :
    commonGCDAtMax
        (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b *
      commonQuotientLinear D w0 L s m nodes u0 u1 b hH z =
      kernelReconstructLinear D w0 L s m nodes u0 u1 z :=
  mul_mappedFixedFactorQuotientLinearMap _ _ _ _ z

theorem commonQuotientLinear_injective {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0) :
    Function.Injective
      (commonQuotientLinear D w0 L s m nodes u0 u1 b hH) :=
  mappedFixedFactorQuotientLinearMap_injective _ _ _ _
    (kernelReconstructLinear_injective D w0 L s m nodes u0 u1)

private theorem nat_sub_le_of_add_eq_of_le
    {R K0 C B : Nat} (hsum : R + K0 = C) (hr : R ≤ B) : C - B ≤ K0 := by
  apply Nat.sub_le_of_le_add
  rw [← hsum]
  simpa [Nat.add_comm] using Nat.add_le_add_right hr K0

theorem constraintKernel_finrank_lower_bound {I : Type v} [Fintype I]
    (D w0 L s m : Nat) (nodes u0 u1 : I → K) :
    coefficientCount D w0 L s - Fintype.card I * localRankBound m L s ≤
      Module.finrank K
        (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) := by
  let f := constraintMap K D w0 L s m nodes u0 u1
  have hsum := f.finrank_range_add_finrank_ker
  have hrange : Module.finrank K f.range ≤
      Fintype.card I * localRankBound m L s :=
    f.range.finrank_le.trans (globalTarget_finrank_le K m L s)
  have hdom : Module.finrank K (CoefficientIndex D w0 L s → K) =
      coefficientCount D w0 L s := by
    rw [Module.finrank_fintype_fun_eq_card K, coefficient_index_card]
  dsimp [f] at hsum hrange
  rw [hdom] at hsum
  dsimp [ConstraintKernel] at hsum ⊢
  exact nat_sub_le_of_add_eq_of_le hsum hrange

theorem finrank_le_quotient_box {I : Type v} [Fintype I]
    (D w0 L s m Dq Lq sq : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (hmem : ∀ z,
      commonQuotientLinear D w0 L s m nodes u0 u1 b hH z ∈
        globalCoefficientBox K Dq w0 Lq sq) :
    Module.finrank K
        (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) ≤
      coefficientCount Dq w0 Lq sq := by
  let q : ConstraintKernel (K := K) D w0 L s m nodes u0 u1 →ₗ[K]
      globalCoefficientBox K Dq w0 Lq sq :=
    LinearMap.codRestrict (globalCoefficientBox K Dq w0 Lq sq)
      (commonQuotientLinear D w0 L s m nodes u0 u1 b hH) hmem
  have hq : Function.Injective q := by
    intro x y hxy
    apply commonQuotientLinear_injective D w0 L s m nodes u0 u1 b hH
    exact congrArg Subtype.val hxy
  have hle := LinearMap.finrank_le_finrank_of_injective (f := q) hq
  rw [globalCoefficientBox_finrank] at hle
  exact hle

theorem common_divisor_dimension_obstruction {I : Type v} [Fintype I]
    (D w0 L s m Dq Lq sq : Nat) (nodes u0 u1 : I → K)
    {beta : Type w} [Fintype beta]
    (b : Module.Basis beta K
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1))
    (hH : commonGCDAtMax
      (ConstraintKernel (K := K) D w0 L s m nodes u0 u1) b ≠ 0)
    (hmem : ∀ z,
      commonQuotientLinear D w0 L s m nodes u0 u1 b hH z ∈
        globalCoefficientBox K Dq w0 Lq sq) :
    coefficientCount D w0 L s - Fintype.card I * localRankBound m L s ≤
      coefficientCount Dq w0 Lq sq :=
  (constraintKernel_finrank_lower_bound D w0 L s m nodes u0 u1).trans
    (finrank_le_quotient_box D w0 L s m Dq Lq sq nodes u0 u1 b hH hmem)

 

namespace E80270

open ContactTwoTailParameters6750Research

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

abbrev AKernel (u0 u1 : IRSProfile.Index → IRSProfile.Field) :=
  ConstraintKernel (K := IRSProfile.Field)
    8729952 131071 300000 14 48 IRSProfile.domain u0 u1

abbrev BKernel (u0 u1 : IRSProfile.Index → IRSProfile.Field) :=
  ConstraintKernel (K := IRSProfile.Field)
    17096156 131071 1708 29 94 IRSProfile.domain u0 u1

theorem profileA_localRank_exact :
    localRankBound 48 300000 14 = 4084229030 := by
  decide

theorem profileB_localRank_exact :
    localRankBound 94 1708 29 = 169407825 := by
  decide

theorem profileA_coefficient_exact :
    coefficientCount 8729952 131071 300000 14 = 1070799433869570 := by
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
      8729952 131071 300000 14 67 (by decide) (by decide)]
  decide

theorem profileB_coefficient_exact :
    coefficientCount 17096156 131071 1708 29 = 44410627150990 := by
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
      17096156 131071 1708 29 131 (by decide) (by decide)]
  decide

theorem profileA_nullity_exact :
    coefficientCount 8729952 131071 300000 14 -
      262144 * localRankBound 48 300000 14 = 143299029250 := by
  rw [profileA_coefficient_exact, profileA_localRank_exact]

theorem profileB_nullity_exact :
    coefficientCount 17096156 131071 1708 29 -
      262144 * localRankBound 94 1708 29 = 1382274190 := by
  rw [profileB_coefficient_exact, profileB_localRank_exact]

theorem profileB_total_one_quotient_exact :
    coefficientCount 17096156 131071 1 29 = 68122483 := by
  decide

theorem profileA_interpolation_gate :
    Fintype.card IRSProfile.Index * localRankBound 48 300000 14 <
      coefficientCount 8729952 131071 300000 14 := by
  rw [show Fintype.card IRSProfile.Index = 262144 by
    norm_num [IRSProfile.Index]]
  rw [profileA_coefficient_exact, profileA_localRank_exact]
  decide

theorem profileB_interpolation_gate :
    Fintype.card IRSProfile.Index * localRankBound 94 1708 29 <
      coefficientCount 17096156 131071 1708 29 := by
  rw [show Fintype.card IRSProfile.Index = 262144 by
    norm_num [IRSProfile.Index]]
  rw [profileB_coefficient_exact, profileB_localRank_exact]
  decide

private theorem commonGCD_data
    (D L s m : Nat) (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field)
        D 131071 L s m IRSProfile.domain u0 u1)) :
    let V := ConstraintKernel (K := IRSProfile.Field)
      D 131071 L s m IRSProfile.domain u0 u1
    let H := commonGCDAtMax V b
    H ≠ 0 ∧ H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s := by
  dsimp only
  let V := ConstraintKernel (K := IRSProfile.Field)
    D 131071 L s m IRSProfile.domain u0 u1
  let H := commonGCDAtMax V b
  have hH : H ≠ 0 := commonGCDAtMax_ne_zero V b
  let i : beta := Classical.choice inferInstance
  let Qi := reconstruct IRSProfile.Field D 131071 L s (b i).1
  have hQi : Qi ≠ 0 := by
    apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
    intro hz
    apply b.ne_zero i
    exact Subtype.ext hz
  have hQibox : Qi ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
    reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1
  have hHbox : H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
    mem_flagGlobalCoefficientBox_of_dvd H Qi D 131071 L s hQi
      (commonGCDAtMax_dvd_basis V b i) hQibox
  exact ⟨hH, hHbox⟩

theorem profileA_commonGCD_ys_le
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta IRSProfile.Field (AKernel u0 u1)) :
    wt residualYSWeights (commonGCDAtMax (AKernel u0 u1) b) ≤ 66 := by
  let H := commonGCDAtMax (AKernel u0 u1) b
  obtain ⟨hH, hbox⟩ := commonGCD_data 8729952 300000 14 48 u0 u1 b
  have hcaps := (mem_flagGlobalCoefficientBox_iff H
    8729952 131071 300000 14 (by decide)).mp hbox
  have hrel := residualYS_mul_le_contact_add_slope H 131071 (by decide)
  change wt residualYSWeights H ≤ 66
  omega

theorem profileA_commonGCD_slope_le
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    {beta : Type w} [Fintype beta] [Nonempty beta]
    (b : Module.Basis beta IRSProfile.Field (AKernel u0 u1)) :
    wt residualSWeights (commonGCDAtMax (AKernel u0 u1) b) ≤ 14 := by
  let H := commonGCDAtMax (AKernel u0 u1) b
  obtain ⟨hH, hbox⟩ := commonGCD_data 8729952 300000 14 48 u0 u1 b
  exact ((mem_flagGlobalCoefficientBox_iff H
    8729952 131071 300000 14 (by decide)).mp hbox).2.1

end E80270

end


end ProximityPrize.SubmissionLower.ContactKernelCommonGCD6750Research
