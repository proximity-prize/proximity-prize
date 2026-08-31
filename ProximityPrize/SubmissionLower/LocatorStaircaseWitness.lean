import ProximityPrize.SubmissionLower.LocatorStaircaseAvoidance

namespace ProximityPrize.SubmissionLower.LocatorStaircaseWitness

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234
  LocatorLowQuotient LocatorStaircaseAvoidance

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

variable {K I : Type} [Field K] [Fintype I]
local instance : DecidableEq K := Classical.decEq K

/-- Lift the abstract staircase dichotomy to the constraint-kernel
reconstruction.  The first branch lowers the parent once and excludes `F²`;
the conditional second branch lowers it twice and excludes `F³`. -/
theorem exists_fixed_staircase_quotient_finrank
    (D w L s m Ysrc delta cubeBound : ℕ) (nodes u0 u1 : I → K)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw : 1 ≤ w) (hshape : D + s ≤ w * (Ysrc + 1))
    (hcube : coefficientCount
        (D - delta - delta - wt (contactWeights w) F -
          wt (contactWeights w) F - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F -
          wt residualTotalWeights F)
        (s - wt residualSWeights F - wt residualSWeights F -
          wt residualSWeights F) ≤ cubeBound)
    (hsource :
      delta * channelCount
          (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
            (s - wt residualSWeights F) +
        delta * channelCount
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) +
        cubeBound <
      Module.finrank K
        (ConstraintKernel (K := K) D w L s m nodes u0 u1)) :
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
        (Q : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q = reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K
        (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧ ¬ F ∣ Q) ∨
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
        (R : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ R ≠ 0 ∧ F * (F * R) = reconstruct K D w L s v.1 ∧
      R ∈ nestedCoefficientBox K
        (D - delta - delta - wt (contactWeights w) F -
          wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ∧
      F * (F * R) ∈ globalCoefficientBox K (D - delta - delta) w L s ∧
      ¬ F ∣ R) := by
  classical
  let recon := kernelReconstructLinear (K := K) D w L s m nodes u0 u1
  have hdivK : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F hF hdivK
  have hqinj : Function.Injective q :=
    quotientLinear_injective recon
      (kernelReconstructLinear_injective (K := K) D w L s m nodes u0 u1)
      F hF hdivK
  have hprod (v : ConstraintKernel (K := K) D w L s m nodes u0 u1) :
      recon v = F * q v :=
    recon_eq_mul_quotientPolynomial recon F hdivK v
  have hqbox : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      q v ∈ globalCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (s - wt residualSWeights F) :=
    quotient_box_of_full_divisor D w L s m
      (wt (contactWeights w) F) (wt residualTotalWeights F)
      (wt residualSWeights F) nodes u0 u1 F hF hdivK le_rfl le_rfl le_rfl
  have hqYS (v : ConstraintKernel (K := K) D w L s m nodes u0 u1) :
      wt residualYSWeights (q v) ≤ Ysrc - wt residualYSWeights F := by
    by_cases hv : v = 0
    · subst v
      simp [wt, MvPolynomial.weightedTotalDegree]
    · have hqv : q v ≠ 0 := by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc : wt residualYSWeights (recon v) ≤ Ysrc := by
        apply flag_box_ys_bound D w L s Ysrc hw hshape
        change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
        exact reconstruct_mem_globalCoefficientBox K D w L s v.1
      have hmul := weightedTotalDegree_mul residualYSWeights F (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  have hqNested : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      q v ∈ nestedCoefficientBox K (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) := by
    intro v d hd
    have hb := hqbox v hd
    have hy :=
      (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (hqYS v)
    rw [weight_fin4] at hy
    simp only [residualYSWeights] at hy
    refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
    simpa [residualYSWeights] using hy
  have hwidth₁ : D - wt (contactWeights w) F ≤
      (D - delta - wt (contactWeights w) F) + delta := by omega
  have hwidth₂ :
      D - delta - wt (contactWeights w) F - wt (contactWeights w) F ≤
        (D - delta - delta - wt (contactWeights w) F -
          wt (contactWeights w) F) + delta := by omega
  obtain hfirst | hsecond :=
    exists_nonzero_image_mem_staircase_not_dvd
      (D - wt (contactWeights w) F)
      (D - delta - wt (contactWeights w) F)
      (D - delta - delta - wt (contactWeights w) F - wt (contactWeights w) F)
      w delta
      (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
      (s - wt residualSWeights F) cubeBound hwidth₁ q hqinj hqNested F hF
      hwidth₂ hcube hsource
  · obtain ⟨v, hv, hQ, hQbox, hnot⟩ := hfirst
    have heq : F * q v = reconstruct K D w L s v.1 := by
      simpa only [recon, kernelReconstructLinear_apply] using (hprod v).symm
    left
    refine ⟨v, q v, hv, hQ, heq, hQbox, ?_, hnot⟩
    have hsourceBox : F * q v ∈ globalCoefficientBox K D w L s := by
      rw [heq]
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    have hparent : 0 < D - delta := by
      have h := (nested_mem_weights hQbox hQ).2.2.2
      omega
    have hD : 0 < D := by omega
    have hsrc :=
      (mem_flagGlobalCoefficientBox_iff (F * q v) D w L s hD).mp hsourceBox
    have hqc := (nested_mem_weights hQbox hQ).2.2.2
    have hmul := weightedTotalDegree_mul (contactWeights w) F (q v) hF hQ
    apply (mem_flagGlobalCoefficientBox_iff
      (F * q v) (D - delta) w L s hparent).mpr
    refine ⟨hsrc.1, hsrc.2.1, ?_⟩
    simp only [wt] at hqc ⊢
    omega
  · obtain ⟨v, R, hv, hR, hqR, hRbox, hnot⟩ := hsecond
    have heq : F * (F * R) = reconstruct K D w L s v.1 := by
      rw [← hqR]
      simpa only [recon, kernelReconstructLinear_apply] using (hprod v).symm
    right
    refine ⟨v, R, hv, hR, heq, hRbox, ?_, hnot⟩
    have hsourceBox : F * (F * R) ∈ globalCoefficientBox K D w L s := by
      rw [heq]
      exact reconstruct_mem_globalCoefficientBox K D w L s v.1
    have hparent : 0 < D - delta - delta := by
      have h := (nested_mem_weights hRbox hR).2.2.2
      omega
    have hD : 0 < D := by omega
    have hsrc :=
      (mem_flagGlobalCoefficientBox_iff (F * (F * R)) D w L s hD).mp
        hsourceBox
    have hRc := (nested_mem_weights hRbox hR).2.2.2
    have hFR : F * R ≠ 0 := mul_ne_zero hF hR
    have hmul₁ := weightedTotalDegree_mul (contactWeights w) F R hF hR
    have hmul₂ := weightedTotalDegree_mul (contactWeights w) F (F * R) hF hFR
    apply (mem_flagGlobalCoefficientBox_iff
      (F * (F * R)) (D - delta - delta) w L s hparent).mpr
    refine ⟨hsrc.1, hsrc.2.1, ?_⟩
    simp only [wt] at hRc ⊢
    omega

/-- The submission-facing staircase witness.  It combines the two-stage
selection theorem with the constraint-kernel lower bound and supplies the
first- or second-contact vanishing needed by the corresponding resultant
count. -/
theorem exists_fixed_staircase_with_derivative_vanishing
    (D w L s m Ysrc delta cubeBound agreements : ℕ)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw : 1 ≤ w) (hshape : D + s ≤ w * (Ysrc + 1))
    (hcube : coefficientCount
        (D - delta - delta - wt (contactWeights w) F -
          wt (contactWeights w) F - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F -
          wt residualTotalWeights F)
        (s - wt residualSWeights F - wt residualSWeights F -
          wt residualSWeights F) ≤ cubeBound)
    (hsource :
      delta * channelCount
          (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
            (s - wt residualSWeights F) +
        delta * channelCount
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) +
        cubeBound <
      coefficientCount D w L s - Fintype.card I * localRankBound m L s)
    (hcapacity₁ : D - delta ≤ (m - 1) * agreements + (w - 1))
    (hcapacity₂ : D - delta - delta ≤
      (m - 2) * agreements + 2 * (w - 1))
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card) :
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
        (Q : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ Q ≠ 0 ∧ F * Q = reconstruct K D w L s v.1 ∧
      Q ∈ nestedCoefficientBox K
        (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F) (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) ∧
      F * Q ∈ globalCoefficientBox K (D - delta) w L s ∧
      (∀ gamma ∈ Gamma, RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (F * Q)) = 0) ∧ ¬ F ∣ Q) ∨
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
        (R : MvPolynomial (Fin 4) K),
      v ≠ 0 ∧ R ≠ 0 ∧ F * (F * R) = reconstruct K D w L s v.1 ∧
      R ∈ nestedCoefficientBox K
        (D - delta - delta - wt (contactWeights w) F -
          wt (contactWeights w) F) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ∧
      F * (F * R) ∈ globalCoefficientBox K (D - delta - delta) w L s ∧
      (∀ gamma ∈ Gamma, RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4) (F * (F * R)))) = 0) ∧
      ¬ F ∣ R) := by
  obtain hfirst | hsecond := exists_fixed_staircase_quotient_finrank
    D w L s m Ysrc delta cubeBound nodes u0 u1 F hF hdiv hw hshape
    hcube (hsource.trans_le
      (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1))
  · obtain ⟨v, Q, hv, hQ, heq, hQbox, hparent, hnot⟩ := hfirst
    left
    refine ⟨v, Q, hv, hQ, heq, hQbox, hparent, ?_, hnot⟩
    intro gamma hgamma
    let support := (Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    have hcard : agreements ≤ support.card := hagreement gamma hgamma
    have hcap : D - delta ≤ (m - 1) * support.card + (w - 1) :=
      hcapacity₁.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 1) hcard) _)
    have hvalues : ∀ i ∈ support,
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hvbox : reconstruct K D w L s v.1 ∈
        globalCoefficientBox K (D - delta) w L s := by
      rw [← heq]
      exact hparent
    rw [heq]
    exact specialization_pderiv_R_eq_zero_of_kernel_low_box
      D (D - delta) w L s m nodes u0 u1 v hvbox
      (selected gamma) gamma support hw (hdegree gamma hgamma) hcap hvalues
  · obtain ⟨v, R, hv, hR, heq, hRbox, hparent, hnot⟩ := hsecond
    right
    refine ⟨v, R, hv, hR, heq, hRbox, hparent, ?_, hnot⟩
    intro gamma hgamma
    let support := (Finset.univ : Finset I).filter (fun i =>
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    have hcard : agreements ≤ support.card := hagreement gamma hgamma
    have hcap : D - delta - delta ≤
        (m - 2) * support.card + 2 * (w - 1) :=
      hcapacity₂.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 2) hcard) _)
    have hvalues : ∀ i ∈ support,
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hvbox : reconstruct K D w L s v.1 ∈
        globalCoefficientBox K (D - delta - delta) w L s := by
      rw [← heq]
      exact hparent
    rw [heq]
    exact specialization_second_pderiv_R_eq_zero_of_kernel_low_box
      D (D - delta - delta) w L s m nodes u0 u1 v hvbox
      (selected gamma) gamma support hw (hdegree gamma hgamma) hcap hvalues

end

end ProximityPrize.SubmissionLower.LocatorStaircaseWitness
