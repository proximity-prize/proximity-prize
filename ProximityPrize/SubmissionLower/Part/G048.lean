import ProximityPrize.SubmissionLower.Part.G047


section Compact_SecondJetHelperWeights
/-! Exact cumulative degree bounds for the cleared helper. The S-coefficient
slope cancels the numerator's excess weight over the denominator. -/
namespace ProximityPrize.SubmissionLower.SecondJetHelperWeights
open scoped BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem derivative_coefficient_bounds (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (e : Fin 4 →₀ ℕ) (he : e ∈ ((asS ((pderiv 1)^[d] P)).coeff j).support) :
    2*(j+d)+e 2 ≤ B ∧ j+d+e 1+e 2 ≤ U ∧ j+d+e 1+e 2+e 3 ≤ L := by
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  simpa [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4] using hb

theorem derivative_coefficient_weights (P : Poly (K := K)) (B U L d j : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L) :
    wt residualSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ B-2*d-2*j ∧
    wt residualYSWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ U-d-j ∧
    wt residualTotalWeights ((asS ((pderiv 1)^[d] P)).coeff j) ≤ L-d-j := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
    intro e he
    have hb := derivative_coefficient_bounds P B U L d j hP e he
  · simp [residualSWeights,RCN081.weight_fin4]
    omega
  · simp [residualYSWeights,RCN081.weight_fin4]
    omega
  · simp [residualTotalWeights,RCN081.weight_fin4]
    omega

theorem asS_derivative_degree (P : Poly (K := K)) (s d : ℕ)
    (hP : ∀ e ∈ P.support, e 1 ≤ s) :
    (asS ((pderiv 1)^[d] P)).natDegree ≤ s-d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  obtain ⟨e,he⟩ := MvPolynomial.support_nonempty.mpr hn
  have hb := hP _ (SecondJetGlobalDifferentiation.support_iterate P d _
    (coefficient_support ((pderiv 1)^[d] P) j e he))
  have h1 := (lift_coordinates j e).2.1
  simp [Finsupp.add_apply,Finsupp.single_apply,h1] at hb
  omega

theorem cleared_weight (weights : Fin 4 → ℕ) (P : Polynomial (MvPolynomial (Fin 4) K))
    (n C slope Hcap : ℕ) (H G : MvPolynomial (Fin 4) K)
    (hC : slope*n ≤ C)
    (hP : ∀ j : Fin (n+1), wt weights (P.coeff j.val) ≤ C-slope*j.val)
    (hH : wt weights H ≤ Hcap) (hG : wt weights G ≤ Hcap+slope) :
    wt weights (cleared P n H G) ≤ C+n*Hcap := by
  unfold cleared
  apply RCN235.wt_finset_sum_le
  intro j _
  have hj := j.isLt
  have hp := hP j
  have hh := (wt_pow_le weights H (n-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hg := (wt_pow_le weights G j.val).trans (Nat.mul_le_mul_left _ hG)
  have ht := (wt_mul_le weights (P.coeff j.val*H^(n-j.val)) (G^j.val)).trans
    (Nat.add_le_add ((wt_mul_le weights (P.coeff j.val) (H^(n-j.val))).trans
      (Nat.add_le_add hp hh)) hg)
  have hjn : j.val ≤ n := by omega
  have hjC : slope*j.val ≤ C := (Nat.mul_le_mul_left slope hjn).trans hC
  have hc : C-slope*j.val+slope*j.val = C := Nat.sub_add_cancel hjC
  have hn : n-j.val+j.val = n := Nat.sub_add_cancel hjn
  nlinarith

theorem helper_weights (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (B U L s d capT capY capR : ℕ) (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L)
    (hd : d ≤ s) (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT) :
    wt residualSWeights (helper P F (s-d) d) ≤ B-2*d+(s-d)*(capR-1) ∧
    wt residualYSWeights (helper P F (s-d) d) ≤ U-d+(s-d)*(capY-1) ∧
    wt residualTotalWeights (helper P F (s-d) d) ≤ L-d+(s-d)*(capT-1) := by
  have hw (weights : Fin 4 → ℕ) (cap : ℕ) (hR1 : weights 2 = 1)
      (hFcap : wt weights F ≤ cap) : wt weights (2*RCN313.polyH K F) ≤ cap-1 := by
    have hh := wt_polyH_le weights F cap hFcap
    have hm := wt_mul_le weights (2 : MvPolynomial (Fin 4) K) (RCN313.polyH K F)
    have hc : wt weights (2 : MvPolynomial (Fin 4) K) = 0 := wt_natCast weights 2
    rw [hR1] at hh
    omega
  refine ⟨?_,?_,?_⟩
  · apply cleared_weight residualSWeights _ (s-d) (B-2*d) 2 (capR-1) _ _ (by omega)
      (fun j => (derivative_coefficient_weights P B U L d j.val hP).1)
      (hw _ capR rfl hF.1)
    have hg := wt_polyG_le residualSWeights rfl F capR hF.1
    change wt residualSWeights (RCN313.polyG K F) ≤ capR-1+2
    change wt residualSWeights (RCN313.polyG K F) ≤ capR+1 at hg
    omega
  · apply cleared_weight residualYSWeights _ (s-d) (U-d) 1 (capY-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.1)
      (hw _ capY rfl hF.2.1)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualYSWeights rfl F capY (by decide) hY hF.2.1
    omega
  · apply cleared_weight residualTotalWeights _ (s-d) (L-d) 1 (capT-1) _ _ (by omega)
      (fun j => by simpa using (derivative_coefficient_weights P B U L d j.val hP).2.2)
      (hw _ capT rfl hF.2.2)
    have hg := RCN179.wt_polyG_le_of_R_le_Y residualTotalWeights rfl F capT (by decide) hT hF.2.2
    omega

end
end ProximityPrize.SubmissionLower.SecondJetHelperWeights

end Compact_SecondJetHelperWeights
