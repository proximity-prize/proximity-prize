import ProximityPrize.SubmissionLower.MovingSourceLinearSeedAssembly6814

/-! Ordinary moving-cut flags for factors with arbitrary nested weights.
Unlike the older coefficient-flag adapter, this does not assume B<=U
for each factor. It uses the true necessary inequality B<=U+s and
therefore preserves the shared source budget under factorization. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open MvPolynomial RCN095 RCN136 RCN207
open MovingSourceClearing6814 WholeSpaceCube6814 WholeSpaceCubeUniform6814

variable {K E : Type} [Field K] [Field E]
local notation "Poly5" => MvPolynomial (Fin 5) K

def slope (P : Poly5) := weightedTotalDegree slopeWeights P
def middle (P : Poly5) := weightedTotalDegree middleWeights P
def total (P : Poly5) := weightedTotalDegree totalWeights P
def order (P : Poly5) := P.degreeOf 1
def ordinaryFlag (P : Poly5) : FlagDegree := ⟨total P-middle P,middle P+order P-slope P,slope P⟩

theorem source_nested (P : Poly5) :
    middle P≤total P ∧ order P≤middle P ∧ 2*order P≤slope P ∧ slope P≤middle P+order P := by
  have hcoef (e) (he : e∈P.support) :
      e 1+e 2+e 3≤middle P ∧ 2*e 1+e 3≤slope P ∧ e 1≤order P := by
    refine ⟨?_,?_,MvPolynomial.monomial_le_degreeOf _ he⟩
    · simpa [middle,weight_coords,middleWeights] using MvPolynomial.le_weightedTotalDegree middleWeights he
    · simpa [slope,weight_coords,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
  refine ⟨?_,?_,?_,?_⟩
  · apply Finset.sup_le
    intro e he
    have ht : Finsupp.weight totalWeights e≤total P := MvPolynomial.le_weightedTotalDegree totalWeights he
    simp only [weight_coords,middleWeights,totalWeights] at ht ⊢
    simp at ht ⊢
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hh := hcoef e he
    omega
  · have h : order P≤slope P/2 := MvPolynomial.degreeOf_le_iff.mpr (by
      intro e he
      have hh := hcoef e he
      omega)
    omega
  · apply Finset.sup_le
    intro e he
    have hh := hcoef e he
    simp [weight_coords,slopeWeights]
    omega

theorem ordinaryFlag_cumulative (P : Poly5) :
    (ordinaryFlag P).all=slope P ∧
    (ordinaryFlag P).yz+(ordinaryFlag P).all=middle P+order P ∧
    (ordinaryFlag P).zOnly+(ordinaryFlag P).yz+(ordinaryFlag P).all=total P+order P := by
  have hh := source_nested P
  dsimp only [ordinaryFlag]
  omega

private theorem cleared_weight
    (w : Fin 3 → ℕ) (P : Polynomial (MvPolynomial (Fin 3) E))
    (s cap drop a b : ℕ) (hcap : drop*s≤cap) (hbalance : drop+a=b)
    (H Q : MvPolynomial (Fin 3) E)
    (hP : ∀ j : Fin (s+1), RCN372.wt w (P.coeff j.val)≤cap-drop*j.val)
    (hH : RCN372.wt w H≤a) (hQ : RCN372.wt w Q≤b) :
    RCN372.wt w (SecondJetClearedHelper.cleared P s H Q)≤cap+s*a := by
  unfold SecondJetClearedHelper.cleared
  apply RCN372.wt_finset_sum_le
  intro j _
  have hp := hP j
  have hh := (RCN372.wt_pow_le w H (s-j.val)).trans (Nat.mul_le_mul_left _ hH)
  have hq := (RCN372.wt_pow_le w Q j.val).trans (Nat.mul_le_mul_left _ hQ)
  have hm := RCN372.wt_mul_le w (P.coeff j.val) (H^(s-j.val))
  have hn := RCN372.wt_mul_le w (P.coeff j.val*H^(s-j.val)) (Q^j.val)
  have hj : j.val≤s := Nat.le_of_lt_succ j.isLt
  have hsub := Nat.sub_add_cancel ((Nat.mul_le_mul_left drop hj).trans hcap)
  have hs := Nat.sub_add_cancel hj
  nlinarith

theorem coefficient_weights
    (phi : Polynomial K →+* E) (P : Poly5) (j : ℕ) :
    RCN372.wt RCN125.sWeight ((coefficients phi P).coeff j)≤slope P-2*j ∧
    RCN372.wt RCN125.ysWeight ((coefficients phi P).coeff j)≤middle P-j ∧
    RCN372.wt RCN125.totalWeight ((coefficients phi P).coeff j)≤total P-j := by
  have hb : ∀ e∈P.support, 2*e 1+e 3≤slope P ∧ e 1+e 2+e 3≤middle P ∧
      e 1+e 2+e 3+e 4≤total P := by
    intro e he
    refine ⟨?_,?_,?_⟩
    · simpa [slope,weight_coords,slopeWeights,Nat.mul_comm] using MvPolynomial.le_weightedTotalDegree slopeWeights he
    · simpa [middle,weight_coords,middleWeights] using MvPolynomial.le_weightedTotalDegree middleWeights he
    · simpa [total,weight_coords,totalWeights] using MvPolynomial.le_weightedTotalDegree totalWeights he
  have hw := SecondJetHelperWeights.derivative_coefficient_weights P (slope P) (middle P) (total P) 0 j hb
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  have hs := RCN130.surfaceMap_nested_weights_le phi ((SecondJetCoefficients.asS P).coeff j)
  rw [coefficients,Polynomial.coeff_map]
  exact ⟨hs.1.trans hw.1,hs.2.1.trans hw.2.1,hs.2.2.trans hw.2.2⟩

theorem movingCut_ordinaryFlag
    (phi : Polynomial K →+* E) (P : Poly5)
    (Q A : MvPolynomial (Fin 3) E) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A) :
    PolynomialInFlag (ordinaryFlag P) (movingCut phi P (order P) Q A target) := by
  have hn := source_nested P
  have hcoeff := coefficient_weights phi P
  have hAf := twice_linear_flag A hA
  have hQf := inFlag_sub_poly (inFlag_const (2 • unitAllFlag) target) hQ
  have hR := cleared_weight RCN125.sWeight (coefficients phi P) (order P) (slope P) 2 0 2
    hn.2.2.1 rfl (2*A) (MvPolynomial.C target-Q) (fun j => (hcoeff j.val).1)
    (RCN125.wt_s_le_of_inFlag hAf) (RCN125.wt_s_le_of_inFlag hQf)
  have hM := cleared_weight RCN125.ysWeight (coefficients phi P) (order P) (middle P) 1 1 2
    (by simpa using hn.2.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j => by simpa only [one_mul] using (hcoeff j.val).2.1)
    (RCN125.wt_ys_le_of_inFlag hAf) (RCN125.wt_ys_le_of_inFlag hQf)
  have hT := cleared_weight RCN125.totalWeight (coefficients phi P) (order P) (total P) 1 1 2
    (by simpa using hn.2.1.trans hn.1) rfl (2*A) (MvPolynomial.C target-Q) (fun j => by simpa only [one_mul] using (hcoeff j.val).2.2)
    (RCN125.wt_total_le_of_inFlag hAf) (RCN125.wt_total_le_of_inFlag hQf)
  intro e he
  have er := (MvPolynomial.le_weightedTotalDegree RCN125.sWeight he).trans hR
  have em := (MvPolynomial.le_weightedTotalDegree RCN125.ysWeight he).trans hM
  have et := (MvPolynomial.le_weightedTotalDegree RCN125.totalWeight he).trans hT
  rw [RCN372.weight_fin3] at er em et
  simp [RCN125.sWeight,RCN125.ysWeight,RCN125.totalWeight] at er em et
  have hc := ordinaryFlag_cumulative P
  change e 1≤_ ∧ e 0+e 1≤_ ∧ e 0+e 1+e 2≤_
  rw [hc.2.2,hc.2.1,hc.1]
  exact ⟨er,em,et⟩

#print axioms source_nested
#print axioms movingCut_ordinaryFlag
end
end ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814
