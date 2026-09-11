import ProximityPrize.SubmissionLower.Part.G045


section Compact_SecondJetCoefficientSpecialization
/-! Coefficient and evaluation identities for the second-derivative variable. -/
namespace ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem lift_succ (j : ℕ) (d : Fin 4 →₀ ℕ) :
    liftExponent (j+1) d = liftExponent j d+Finsupp.single 1 1 := by
  ext i
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j d
  obtain ⟨g0,g1,g2,g3,g4⟩ := lift_coordinates (j+1) d
  fin_cases i <;> simp [Finsupp.add_apply,Finsupp.single_apply,h0,h1,h2,h3,h4,g0,g1,g2,g3,g4]

theorem asS_pderiv (P : Poly (K := K)) :
    asS (pderiv 1 P) = (asS P).derivative := by
  ext j d
  rw [asS_coeff, MvPolynomial.coeff_pderiv, Polynomial.coeff_derivative]
  rw [show ((j : MvPolynomial (Fin 4) K)+1) = MvPolynomial.C (j+1 : K) by simp,
    mul_comm ((asS P).coeff (j+1)) (MvPolynomial.C (j+1 : K)),
    MvPolynomial.coeff_C_mul, asS_coeff]
  rw [← lift_succ, (lift_coordinates j d).2.1]
  simp [mul_comm]

theorem asS_iterate (P : Poly (K := K)) (d : ℕ) :
    asS ((pderiv 1)^[d] P) = (Polynomial.derivative)^[d] (asS P) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', asS_pderiv, ih]

def coefficientSpecialize (f : Polynomial K) (z : K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,f,f.derivative,Polynomial.C z]

def evaluateS (f : Polynomial K) (z : K) :
    Polynomial (MvPolynomial (Fin 4) K) →ₐ[K] Polynomial K :=
  { Polynomial.eval₂RingHom (coefficientSpecialize f z).toRingHom (Polynomial.hasseDeriv 2 f) with
    commutes' := by intro c; simp [coefficientSpecialize] }

theorem specialize_eq (P : Poly (K := K)) (f : Polynomial K) (z : K) :
    specialize f z P = (asS P).eval₂ (coefficientSpecialize f z).toRingHom
      (Polynomial.hasseDeriv 2 f) := by
  have heq : specialize f z = (evaluateS f z).comp (asS (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (1 : Fin 5) = g 0 := rfl
    have h2 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (2 : Fin 5) = g 1 := rfl
    have h3 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (3 : Fin 5) = g 2 := rfl
    have h4 (A : Polynomial (MvPolynomial (Fin 4) K)) (g : Fin 4 → Polynomial (MvPolynomial (Fin 4) K)) :
        Fin.cases A g (4 : Fin 5) = g 3 := rfl
    fin_cases i <;> simp [specialize, asS, coefficientSpecialize, evaluateS,
      Equiv.swap_apply_def, MvPolynomial.finSuccEquiv_apply, h1,h2,h3,h4]
  exact DFunLike.congr_fun heq P

end
end ProximityPrize.SubmissionLower.SecondJetCoefficientSpecialization

end Compact_SecondJetCoefficientSpecialization
