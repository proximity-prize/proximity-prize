import ProximityPrize.SubmissionLower.RetainedWholeSpace6814

/-! Research controls for the parameter-dependent curvature preflight.
No hypothesis here asserts the proposed full counting theorem. -/
namespace ProximityPrize.SubmissionLower.ParameterCurvature6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The inexpensive quadratic graph in twice-curvature. For
`a=gamma^M`, this vanishes modulo `R-gamma^(2M+1)-Y*gamma^M`. -/
theorem quadratic_graph_identity
    {E : Type*} [CommRing E] (z a y r : E) :
    z*(a*r)^2+y*r*(a*r)-r^3 = -r^2*(r-z*a^2-y*a) := by
  ring

/-- No rational representative of X^M with both degrees below M exists
modulo a polynomial of degree 2M+1. This is a degree argument, not a
numerical search for rational approximants. -/
theorem no_small_rational_representative
    {E : Type*} [Field E] (F H G : Polynomial E) (M : ℕ)
    (hF : F.natDegree=2*M+1) (hH : H≠0)
    (hHd : H.natDegree<M) (hGd : G.natDegree<M) :
    ¬ F ∣ Polynomial.X^M*H-G := by
  have hd : (Polynomial.X^M*H).natDegree=H.natDegree+M :=
    Polynomial.natDegree_X_pow_mul M hH
  have hlt : G.natDegree < (Polynomial.X^M*H).natDegree := by
    rw [hd]
    omega
  have hsub : (Polynomial.X^M*H-G).natDegree=H.natDegree+M := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt,hd]
  have hne : Polynomial.X^M*H-G≠0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hsub
    omega
  intro hdiv
  have hbound := Polynomial.natDegree_le_of_dvd hdiv hne
  rw [hF,hsub] at hbound
  omega

/-- Basic degree-gap threshold of saved source 27; this is conditional
on possessing a rational representative of parameter degree q. -/
theorem source27_parameter_gate (q : ℕ) :
    995+14*q<3504 ↔ q≤179 := by omega

#print axioms quadratic_graph_identity
#print axioms no_small_rational_representative
#print axioms source27_parameter_gate
end
end ProximityPrize.SubmissionLower.ParameterCurvature6814
