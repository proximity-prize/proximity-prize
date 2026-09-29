import ProximityPrize.SubmissionLower.MovingSourceLinearFlow6814

/-! Actual numerator recurrence for an arbitrary rational curvature flow.
Its field semantics and the original numerator specialization are proved. -/
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN313 MovingSourceLinearFlow6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

def step (H G : Poly) (n : ℕ) (P : Poly) : Poly :=
  clearedStep (2*n) P (pderiv 0 P) (pderiv 1 P) (pderiv 2 P)
    (MvPolynomial.X 2) G H (pderiv 0 H) (pderiv 1 H) (pderiv 2 H)

def numerators (H G : Poly) : ℕ → Poly
  | 0 => MvPolynomial.X 1
  | n+1 => step H G n (numerators H G n)

theorem step_eq (H G P : Poly) (n : ℕ) :
    step H G n P=H*flow H G P-(2*n : ℕ)*P*flow H G H := by
  simp only [step,clearedStep,flow_apply]
  ring

theorem old_numerators (F : Poly) (n : ℕ) :
    numerators (polyH K F) (polyG K F) n=numerator K F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [numerators,ih,numerator_succ]
    rfl

theorem iterate_eq_fraction
    {E : Type} [Field E] [Algebra K E]
    (D : Derivation K E E) (phi : Poly →+* E) (H G : Poly) (hH : phi H≠0)
    (hchain : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P)) (n : ℕ) :
    D^[n] (phi (MvPolynomial.X 1))=phi (numerators H G n)*(phi H)⁻¹^(2*n) := by
  induction n with
  | zero => simp [numerators]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,numerators,step,map_clearedStep]
    have hu : D ((phi H)⁻¹)= -((phi H)⁻¹^2*
        (phi (pderiv 0 H)+phi (MvPolynomial.X 2)*phi (pderiv 1 H)+
          phi G*(phi H)⁻¹*phi (pderiv 2 H))) := by
      rw [D.leibniz_inv,hchain H]
      simp only [smul_eq_mul,neg_mul]
    have hh := differentiated_fraction_step D (2*n)
      (phi (numerators H G n)) (phi (pderiv 0 (numerators H G n)))
      (phi (pderiv 1 (numerators H G n))) (phi (pderiv 2 (numerators H G n)))
      (phi (MvPolynomial.X 2)) (phi G) (phi H)
      (phi (pderiv 0 H)) (phi (pderiv 1 H)) (phi (pderiv 2 H)) ((phi H)⁻¹)
      (mul_inv_cancel₀ hH) (hchain _) hu
    simpa only [show 2*(n+1)=2*n+2 by omega] using hh

theorem numerator_cross_eq
    {E : Type} [Field E] [Algebra K E]
    (D : Derivation K E E) (phi : Poly →+* E) (H G H' G' : Poly)
    (hH : phi H≠0) (hH' : phi H'≠0)
    (hchain : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G*(phi H)⁻¹*phi (pderiv 2 P))
    (hchain' : ∀ P, D (phi P)=phi (pderiv 0 P)+phi (MvPolynomial.X 2)*phi (pderiv 1 P)+
      phi G'*(phi H')⁻¹*phi (pderiv 2 P)) (n : ℕ) :
    phi (numerators H G n)*(phi H')^(2*n)=phi (numerators H' G' n)*(phi H)^(2*n) := by
  have hh := (iterate_eq_fraction D phi H G hH hchain n).symm.trans
    (iterate_eq_fraction D phi H' G' hH' hchain' n)
  have he : phi (numerators H G n)/(phi H)^(2*n)=
      phi (numerators H' G' n)/(phi H')^(2*n) := by
    simpa only [div_eq_mul_inv,inv_pow] using hh
  exact (div_eq_div_iff (pow_ne_zero _ hH) (pow_ne_zero _ hH')).mp he

#print axioms iterate_eq_fraction
#print axioms numerator_cross_eq
end
end ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
