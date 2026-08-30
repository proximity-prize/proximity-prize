import ProximityPrize.SubmissionLower.TwoKernelSelection
/- Uncompiled research draft. The bare import names the sibling research
   file; rewrite it to a permitted SubmissionLower import only at integration. -/
namespace ProximityPrize.SubmissionLower.TwoKernelCaps
open ProximityPrize.Benchmark
open RCN180 RCN100
open RCN119 RCN130
open RCN081 RCN234
open RCN156 TwoKernelSelection
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

theorem quotient_box_of_full_divisor
    {K I : Type*} [Field K] [Fintype I]
    (D w L s m c t r : ℕ) (x u0 u1 : I → K)
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m x u0 u1,
      H ∣ kernelReconstructLinear (K := K) D w L s m x u0 u1 v)
    (hc : c ≤ wt (contactWeights w) H)
    (ht : t ≤ wt residualTotalWeights H) (hr : r ≤ wt residualSWeights H) :
    ∀ v : ConstraintKernel (K := K) D w L s m x u0 u1,
      quotientPolynomial (kernelReconstructLinear (K := K) D w L s m x u0 u1)
        H hdiv v ∈ globalCoefficientBox K (D - c) w (L - t) (s - r) := by
  let recon := kernelReconstructLinear (K := K) D w L s m x u0 u1
  intro v
  by_cases hv : v = 0
  · subst v
    have hz : quotientPolynomial recon H hdiv 0 = 0 :=
      (quotientLinear recon H hH hdiv).map_zero
    rw [hz]
    exact (globalCoefficientBox K _ _ _ _).zero_mem
  · have hQ : recon v ≠ 0 := by
      intro hz
      apply hv
      apply kernelReconstructLinear_injective (K := K) D w L s m x u0 u1
      simpa only [map_zero] using hz
    have heq := recon_eq_mul_quotientPolynomial recon H hdiv v
    have hq : quotientPolynomial recon H hdiv v ≠ 0 := by
      intro hz
      exact hQ (by rw [heq, hz, mul_zero])
    have hReconBox : recon v ∈ globalCoefficientBox K D w L s := by
      change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
      (recon v) H (quotientPolynomial recon H hdiv v)
      D w L s c t r hQ hH hq
      hReconBox heq hc ht hr

theorem small_A_box : coefficientCount 174309 131071 239943 12 = 62573949507 := by
  rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
    174309 131071 239943 12 2 (by decide) (by decide)]
  decide

theorem common_A_ys_le
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hbox : H ∈ globalCoefficientBox K 7645344 131071 240000 12)
    (hdiv : ∀ v : AKernel u0 u1,
      H ∣ reconstruct K 7645344 131071 240000 12 v.1) :
    wt residualYSWeights H ≤ 56 := by
  by_contra hnot
  have hy : 57 ≤ wt residualYSWeights H := by omega
  have hcaps := (mem_flagGlobalCoefficientBox_iff H
    7645344 131071 240000 12 (by decide)).mp hbox
  have hslope : wt residualSWeights H ≤ 12 := hcaps.2.1
  have hw := residualYS_mul_le_contact_add_slope H 131071 (by decide)
  have hc : 57 * 131071 - 12 ≤ wt (contactWeights 131071) H := by omega
  have ht : 57 ≤ wt residualTotalWeights H :=
    hy.trans (residual_weight_nested H).2
  have hdivK : ∀ v : AKernel u0 u1,
      H ∣ kernelReconstructLinear (K := K)
        7645344 131071 240000 12 42 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq := quotient_box_of_full_divisor
    7645344 131071 240000 12 42 (57 * 131071 - 12) 57 0
    IRSProfile.domain u0 u1 H hH hdivK hc ht (Nat.zero_le _)
  have hobs := common_divisor_dimension_obstruction (K := K)
    7645344 131071 240000 12 42 174309 239943 12
    IRSProfile.domain u0 u1 H hH hdivK hq
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    RegularColonArithmetic.kernelA_nullity, small_A_box] at hobs
  omega

theorem common_B_total_le
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hdiv : ∀ v : BKernel u0 u1,
      H ∣ reconstruct K 14744592 131071 1283 25 v.1) :
    wt residualTotalWeights H ≤ 1282 := by
  by_contra hnot
  have ht : 1283 ≤ wt residualTotalWeights H := by omega
  have hdivK : ∀ v : BKernel u0 u1,
      H ∣ kernelReconstructLinear (K := K)
        14744592 131071 1283 25 81 IRSProfile.domain u0 u1 v := by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq := quotient_box_of_full_divisor
    14744592 131071 1283 25 81 0 1283 0
    IRSProfile.domain u0 u1 H hH hdivK (Nat.zero_le _) ht (Nat.zero_le _)
  have hobs := common_divisor_dimension_obstruction (K := K)
    14744592 131071 1283 25 81 14744592 0 25
    IRSProfile.domain u0 u1 H hH hdivK hq
  simp only [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
    RegularColonArithmetic.kernelB_nullity,
    show coefficientCount 14744592 131071 0 25 = 14744592 by decide] at hobs
  omega

namespace SelectedPair
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_caps {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 56 ∧
      wt residualTotalWeights (gcd S.QA S.QB) ≤ 1282 := by
  have hn : gcd S.QA S.QB ≠ 0 := gcd_ne_zero_of_left S.QA_ne
  have hb := mem_flagGlobalCoefficientBox_of_dvd
    (gcd S.QA S.QB) S.QA 7645344 131071 240000 12
    S.QA_ne (gcd_dvd_left _ _) S.QA_flag
  exact ⟨common_A_ys_le u0 u1 _ hn hb S.common_divides_A,
    common_B_total_le u0 u1 _ hn S.common_divides_B⟩
end SelectedPair
end
end ProximityPrize.SubmissionLower.TwoKernelCaps
