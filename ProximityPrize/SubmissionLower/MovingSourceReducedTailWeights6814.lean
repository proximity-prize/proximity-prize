import ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814

/-! Degree bounds for the actual replacement tails, proved by the
recurrence. No expansion of the 131072nd polynomial is performed. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem product_derivative_weight
    (w : Fin 4 → ℕ) (A P : Poly) (i : Fin 4) (c d : ℕ)
    (hA : wt w A≤d+w i) (hP : wt w P≤c) :
    wt w (A*pderiv i P)≤c+d := by
  by_cases hi : w i≤c
  · have hp := wt_pderiv_le w P i c hP
    have hm := wt_mul_le w A (pderiv i P)
    omega
  · have hz : pderiv i P=0 := RCN262.pderiv_eq_zero_of_wt_lt w P i (hP.trans_lt (by omega))
    rw [hz,mul_zero]
    simp [wt,MvPolynomial.weightedTotalDegree]

theorem flow_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (flow H G P)≤c+d := by
  have hRH : wt w (MvPolynomial.X 2*H)≤d+w 1 := by
    have hh := wt_mul_le w (MvPolynomial.X 2) H
    rw [wt_X] at hh
    omega
  have h0 := product_derivative_weight w H P 0 c d (hH.trans hx) hP
  have h1 := product_derivative_weight w (MvPolynomial.X 2*H) P 1 c d hRH hP
  have h2 := product_derivative_weight w G P 2 c d hG hP
  have he : flow H G P=H*pderiv 0 P+(MvPolynomial.X 2*H)*pderiv 1 P+G*pderiv 2 P := by
    rw [flow_apply]
    ring
  rw [he]
  exact (wt_add_le w _ _).trans (max_le
    ((wt_add_le w _ _).trans (max_le h0 h1)) h2)

theorem step_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d n : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (step H G n P)≤c+(h+d) := by
  have hDP := flow_weight w H G P c h d hH hG hx hy hP
  have hDH := flow_weight w H G H h h d hH hG hx hy hH
  have hleft := wt_mul_le w H (flow H G P)
  have hscale := wt_mul_le w ((2*n : ℕ) : Poly) P
  rw [wt_natCast,zero_add] at hscale
  have hright := wt_mul_le w (((2*n : ℕ) : Poly)*P) (flow H G H)
  rw [step_eq]
  exact (wt_sub_le w _ _).trans (max_le (by omega) (by omega))

theorem numerator_weight
    (w : Fin 4 → ℕ) (H G : Poly) (h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (n : ℕ) :
    wt w (numerators H G n)≤w 1+n*(h+d) := by
  induction n with
  | zero => simp [numerators,wt_X]
  | succ n ih =>
    have hh := step_weight w H G (numerators H G n) (w 1+n*(h+d)) h d n hH hG hx hy ih
    change wt w (step H G n (numerators H G n))≤_
    convert hh using 1; ring

theorem linear_tail_weights
    (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331)
    (n : ℕ) :
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤11*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+48*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n := by
  have hh := linear_coefficient_weights J 7 25 331 hshape
  have hR := numerator_weight residualSWeights (linearH J) (linearG J) 5 6
    hh.1.1 hh.2.1 (by decide) (by decide) n
  have hY := numerator_weight residualYSWeights (linearH J) (linearG J) 24 24
    hh.1.2.1 hh.2.2.1 (by decide) (by decide) n
  have hT := numerator_weight residualTotalWeights (linearH J) (linearG J) 330 330
    hh.1.2.2 hh.2.2.2 (by decide) (by decide) n
  refine ⟨?_,?_,?_⟩
  · simpa only [show residualSWeights 1=0 from rfl,zero_add,Nat.reduceAdd,Nat.mul_comm] using hR
  · simpa only [show residualYSWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hY
  · simpa only [show residualTotalWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hT

theorem first_tail_weights
    (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331) :
    wt residualSWeights (numerators (linearH J) (linearG J) 131072)≤1441792 ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) 131072)≤6291457 ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) 131072)≤86507521 := by
  exact linear_tail_weights J hshape 131072

#print axioms linear_tail_weights
#print axioms first_tail_weights
end
end ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
