import ProximityPrize.SubmissionLower.LocatorSecondDerivative6768
import ProximityPrize.SubmissionLower.LocatorCoprimeQuotient

namespace ProximityPrize.SubmissionLower.LocatorFactorSwitchApplication6768

open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN122 RCN130 RCN140 RCN156 RCN180 RCN234
open LocatorLowQuotient LocatorFactorSwitch6768 LocatorSecondDerivative6768

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

variable {K I : Type*} [Field K] [Fintype I]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev P4 := MvPolynomial (Fin 4) K

/-- The exact algebraic handoff from a common kernel factor to either the
ordinary coprime quotient arm or the twice-low cofactor arm. -/
theorem exists_coprime_quotient_or_small_cofactor
    (D w L s m Ysrc delta agreements : Nat)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (F : P4) (hF : F ≠ 0) (hirr : Irreducible F)
    (hdiv : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ reconstruct K D w L s v.1)
    (hw : 1 ≤ w) (hshape : D + s ≤ w * (Ysrc + 1))
    (hsource :
      delta * channelCount
          (L - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) +
        delta * channelCount
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) <
        coefficientCount D w L s - Fintype.card I * localRankBound m L s)
    (hsourceSmall :
      delta * channelCount
          (L - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) +
        coefficientCount delta w
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) <
        coefficientCount D w L s - Fintype.card I * localRankBound m L s)
    (hwidth₁ : D - wt (contactWeights w) F ≤
      (D - delta - wt (contactWeights w) F) + delta)
    (hcapacity₁ : D - delta ≤ (m - 1) * agreements + (w - 1))
    (hcapacity₂ : D - 2 * delta ≤ (m - 2) * agreements + 2 * (w - 1))
    (hcofactor :
      L - wt residualTotalWeights F - wt residualTotalWeights F <
          wt residualTotalWeights F ∨
        Ysrc - wt residualYSWeights F - wt residualYSWeights F <
          wt residualYSWeights F ∨
        s - wt residualSWeights F - wt residualSWeights F <
          wt residualSWeights F)
    (htwo : (2 : K) ≠ 0)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)).card)
    (hroot : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1) (Q : P4),
      v ≠ 0 ∧ Q ≠ 0 ∧ IsRelPrime F Q ∧
      reconstruct K D w L s v.1 = F * Q ∧
      Q ∈ nestedCoefficientBox K
        (D - delta - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F)
        (Ysrc - wt residualYSWeights F)
        (s - wt residualSWeights F) ∧
      reconstruct K D w L s v.1 ∈ globalCoefficientBox K (D - delta) w L s ∧
      ∀ gamma ∈ seeds, specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (reconstruct K D w L s v.1)) = 0) ∨
    (∃ (v : ConstraintKernel (K := K) D w L s m nodes u0 u1) (C : P4),
      v ≠ 0 ∧ C ≠ 0 ∧ IsRelPrime F C ∧
      reconstruct K D w L s v.1 = F * F * C ∧
      C ∈ nestedCoefficientBox K
        (D - delta - wt (contactWeights w) F - wt (contactWeights w) F - delta) w
        (L - wt residualTotalWeights F - wt residualTotalWeights F)
        (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
        (s - wt residualSWeights F - wt residualSWeights F) ∧
      reconstruct K D w L s v.1 ∈ globalCoefficientBox K (D - 2 * delta) w L s ∧
      ∀ gamma ∈ seeds, specialization K (selected gamma) gamma C = 0) := by
  classical
  let recon := kernelReconstructLinear (K := K) D w L s m nodes u0 u1
  have hdivK : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      F ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) D w L s m nodes u0 u1)
    F hF hdivK
  have hprod (v : ConstraintKernel (K := K) D w L s m nodes u0 u1) :
      recon v = F * q v := recon_eq_mul_quotientPolynomial recon F hdivK v
  have hqmem : ∀ v : ConstraintKernel (K := K) D w L s m nodes u0 u1,
      q v ∈ nestedCoefficientBox K
        (D - wt (contactWeights w) F) w
        (L - wt residualTotalWeights F)
        (Ysrc - wt residualYSWeights F)
        (s - wt residualSWeights F) := by
    intro v
    by_cases hv : v = 0
    · subst v
      rw [map_zero]
      exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
    · have hqv : q v ≠ 0 := by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hrv : recon v ≠ 0 := by
        rw [hprod v]
        exact mul_ne_zero hF hqv
      have hglobal : recon v ∈ globalCoefficientBox K D w L s := by
        change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
        exact reconstruct_mem_globalCoefficientBox K D w L s v.1
      have hys : wt residualYSWeights (recon v) ≤ Ysrc :=
        flag_box_ys_bound D w L s Ysrc hw hshape (recon v) hglobal
      have hnested : recon v ∈ nestedCoefficientBox K D w L Ysrc s :=
        mem_nested_of_global_and_ys (recon v) D w L Ysrc s hglobal hys
      exact quotient_mem_nested_of_mul_eq (recon v) F (q v)
        D w L Ysrc s
        (wt (contactWeights w) F) (wt residualTotalWeights F)
        (wt residualYSWeights F) (wt residualSWeights F)
        hnested hF hqv (hprod v) le_rfl le_rfl le_rfl le_rfl
  have hsource' :
      delta * channelCount
          (L - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) +
        delta * channelCount
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F - wt residualYSWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) <
        Module.finrank K
          (ConstraintKernel (K := K) D w L s m nodes u0 u1) :=
    hsource.trans_le (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1)
  have hsourceSmall' :
      delta * channelCount
          (L - wt residualTotalWeights F)
          (Ysrc - wt residualYSWeights F)
          (s - wt residualSWeights F) +
        coefficientCount delta w
          (L - wt residualTotalWeights F - wt residualTotalWeights F)
          (s - wt residualSWeights F - wt residualSWeights F) <
        Module.finrank K
          (ConstraintKernel (K := K) D w L s m nodes u0 u1) :=
    hsourceSmall.trans_le (constraintKernel_finrank_lower_bound D w L s m nodes u0 u1)
  obtain ⟨v, hv, hqv, hswitch⟩ := exists_coprime_or_twice_low_flexible
    (D - wt (contactWeights w) F)
    (D - delta - wt (contactWeights w) F) w delta
    (L - wt residualTotalWeights F)
    (Ysrc - wt residualYSWeights F)
    (s - wt residualSWeights F)
    (wt (contactWeights w) F) (wt residualTotalWeights F)
    (wt residualYSWeights F) (wt residualSWeights F)
    q hqinj hqmem F hF le_rfl le_rfl le_rfl le_rfl
    hwidth₁ hsource' hsourceSmall'
  have hreconNe : recon v ≠ 0 := by
    rw [hprod v]
    exact mul_ne_zero hF hqv
  have hsourceBox : recon v ∈ globalCoefficientBox K D w L s := by
    change reconstruct K D w L s v.1 ∈ globalCoefficientBox K D w L s
    exact reconstruct_mem_globalCoefficientBox K D w L s v.1
  have hDposSource : 0 < D := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hreconNe
    have h := (hsourceBox hd).2.2
    omega
  have hsourceWeights :=
    (mem_flagGlobalCoefficientBox_iff (recon v) D w L s hDposSource).mp hsourceBox
  rcases hswitch with ⟨hQbox, hnot⟩ | ⟨C, hC, hqeq, hCbox⟩
  · have hrel : IsRelPrime F (q v) := hirr.isRelPrime_iff_not_dvd.mpr hnot
    have hQweights := nested_mem_weights hQbox hqv
    have hmulC := weightedTotalDegree_mul (contactWeights w) F (q v) hF hqv
    have hDpos : 0 < D - delta := by omega
    have hparent : recon v ∈ globalCoefficientBox K (D - delta) w L s := by
      apply (mem_flagGlobalCoefficientBox_iff (recon v) (D - delta) w L s hDpos).mpr
      refine ⟨hsourceWeights.1, hsourceWeights.2.1, ?_⟩
      have hcontact : wt (contactWeights w) (recon v) =
          wt (contactWeights w) F + wt (contactWeights w) (q v) := by
        rw [hprod v]
        exact hmulC
      simp only [wt] at hQweights hcontact hsourceWeights ⊢
      omega
    have hvanish : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (recon v)) = 0 := by
      intro gamma hgamma
      let support := (Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
      have hcard : agreements ≤ support.card := hagreement gamma hgamma
      have hcap : D - delta ≤ (m - 1) * support.card + (w - 1) :=
        hcapacity₁.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 1) hcard) _)
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      change specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4)
          (reconstruct K D w L s v.1)) = 0
      exact specialization_pderiv_R_eq_zero_of_kernel_low_box
        D (D - delta) w L s m nodes u0 u1 v hparent
        (selected gamma) gamma support hw (hdegree gamma hgamma) hcap hvalues
    exact Or.inl ⟨v, q v, hv, hqv, hrel,
      by simpa only [recon, kernelReconstructLinear_apply] using hprod v,
      hQbox,
      by simpa only [recon, kernelReconstructLinear_apply] using hparent,
      hvanish⟩
  · have hCweights := nested_mem_weights hCbox hC
    have hFC : F * F ≠ 0 := mul_ne_zero hF hF
    have hmulC₁ := weightedTotalDegree_mul (contactWeights w) F F hF hF
    have hmulC₂ := weightedTotalDegree_mul (contactWeights w) (F * F) C hFC hC
    have hrecon : recon v = F * F * C := by
      calc
        recon v = F * q v := hprod v
        _ = F * (F * C) := by rw [hqeq]
        _ = F * F * C := by ring
    have hrel : IsRelPrime F C := by
      apply hirr.isRelPrime_iff_not_dvd.mpr
      intro hFCdvd
      rcases hcofactor with hT | hY | hS
      · have hle := weightedTotalDegree_le_of_dvd residualTotalWeights F C hFCdvd hC
        change wt residualTotalWeights F ≤ wt residualTotalWeights C at hle
        omega
      · have hle := weightedTotalDegree_le_of_dvd residualYSWeights F C hFCdvd hC
        change wt residualYSWeights F ≤ wt residualYSWeights C at hle
        omega
      · have hle := weightedTotalDegree_le_of_dvd residualSWeights F C hFCdvd hC
        change wt residualSWeights F ≤ wt residualSWeights C at hle
        omega
    have hDpos : 0 < D - 2 * delta := by omega
    have hparent : recon v ∈ globalCoefficientBox K (D - 2 * delta) w L s := by
      apply (mem_flagGlobalCoefficientBox_iff
        (recon v) (D - 2 * delta) w L s hDpos).mpr
      refine ⟨hsourceWeights.1, hsourceWeights.2.1, ?_⟩
      have hcontact : wt (contactWeights w) (recon v) =
          wt (contactWeights w) F + wt (contactWeights w) F +
            wt (contactWeights w) C := by
        rw [hrecon]
        simp only [wt]
        rw [hmulC₂, hmulC₁]
      simp only [wt] at hCweights hcontact hsourceWeights ⊢
      omega
    have hCroot : ∀ gamma ∈ seeds,
        specialization K (selected gamma) gamma C = 0 := by
      intro gamma hgamma
      let support := (Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
      have hcard : agreements ≤ support.card := hagreement gamma hgamma
      have hcap : D - 2 * delta ≤ (m - 2) * support.card + 2 * (w - 1) :=
        hcapacity₂.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (m - 2) hcard) _)
      have hvalues : ∀ i ∈ support,
          (selected gamma).eval (nodes i) = u0 i + gamma * u1 i := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      have hsecond := specialization_pderiv_R_twice_eq_zero_of_kernel_low_box
        D (D - 2 * delta) w L s m nodes u0 u1 v hparent
        (selected gamma) gamma support hw (hdegree gamma hgamma) hcap hvalues
      have hsecond' : specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4) (F * F * C))) = 0 := by
        have hrecon' : reconstruct K D w L s v.1 = F * F * C := by
          simpa only [recon, kernelReconstructLinear_apply] using hrecon
        rw [hrecon'] at hsecond
        exact hsecond
      apply cofactor_specialization_eq_zero F C (selected gamma) gamma
        htwo
        (hroot gamma hgamma) (hregular gamma hgamma) hsecond'
    exact Or.inr ⟨v, C, hv, hC, hrel,
      by simpa only [recon, kernelReconstructLinear_apply] using hrecon,
      hCbox,
      by simpa only [recon, kernelReconstructLinear_apply] using hparent,
      hCroot⟩

end

end ProximityPrize.SubmissionLower.LocatorFactorSwitchApplication6768

#print axioms ProximityPrize.SubmissionLower.LocatorFactorSwitchApplication6768.exists_coprime_quotient_or_small_cofactor
