import ProximityPrize.SubmissionLower.PartG030


section Compact_SecondJetDifferentiation
/-! Differentiation in S loses at most one unit of second-jet contact.
The flat target variables are epsilon, S, T, R, Z. -/
namespace ProximityPrize.SubmissionLower.SecondJetDifferentiation
open scoped BigOperators
open MvPolynomial SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def substitute : Poly (K := K) →ₐ[K] Poly (K := K) :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.X 3-MvPolynomial.X 0*MvPolynomial.X 1+
      MvPolynomial.X 0^2*MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem chain_X (j : Fin 5) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 (MvPolynomial.X j)) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) (MvPolynomial.X j))+
        pderiv 2 (substitute (K := K) (MvPolynomial.X j)) := by
  fin_cases j <;> simp [substitute, pderiv_mul, pderiv_pow, Pi.single_apply] <;> ring

theorem chain_rule (P : Poly (K := K)) :
    MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) =
      MvPolynomial.X 0*pderiv 1 (substitute (K := K) P)+
        pderiv 2 (substitute (K := K) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute]
  | add P Q hP hQ =>
    simp only [map_add]
    linear_combination hP+hQ
  | mul_X P j hP =>
    have hX := chain_X (K := K) j
    simp only [pderiv_mul, map_add, map_mul]
    linear_combination substitute (K := K) (MvPolynomial.X j)*hP + substitute (K := K) P*hX

theorem pderiv_preserves_epsilon (P : Poly (K := K)) (j : Fin 5) (hj : j ≠ 0) (m : ℕ)
    (hP : MvPolynomial.X 0^m ∣ P) : MvPolynomial.X 0^m ∣ pderiv j P := by
  obtain ⟨Q,rfl⟩ := hP
  rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (Ne.symm hj)]
  simp only [mul_zero, zero_mul, zero_add]
  exact dvd_mul_right _ _

theorem derivative_contact (P : Poly (K := K)) (m : ℕ)
    (hP : MvPolynomial.X 0^(m+1) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (pderiv 1 P) := by
  have hs := pderiv_preserves_epsilon (substitute (K := K) P) 1 (by decide) (m+1) hP
  have ht := pderiv_preserves_epsilon (substitute (K := K) P) 2 (by decide) (m+1) hP
  have hh : MvPolynomial.X 0^(m+1) ∣
      MvPolynomial.X 0*substitute (K := K) (pderiv 1 P) := by
    rw [chain_rule]
    exact dvd_add (dvd_mul_of_dvd_right hs _) ht
  rw [pow_succ'] at hh
  exact (mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero (0 : Fin 5))).mp hh

theorem iterate_derivative_contact (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) P) :
    MvPolynomial.X 0^m ∣ substitute (K := K) ((pderiv 1)^[d] P) := by
  induction d generalizing P with
  | zero => simpa using hP
  | succ d ih =>
    have hfirst := derivative_contact P (m+d) (by simpa only [Nat.add_assoc] using hP)
    simpa only [Function.iterate_succ_apply] using ih (pderiv 1 P) hfirst

theorem substitute_contact (P : Poly (K := K)) :
    (MvPolynomial.finSuccEquiv K 4) (substitute (K := K) P) =
      SecondJetLocal.contact (K := K) (flatEquiv (K := K) P) := by
  have h0 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (0 : Fin 5)) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have h1 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (1 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 0)
  have h2 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (2 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (1 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 1)
  have h3 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (3 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (2 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 2)
  have h4 : (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X (4 : Fin 5)) =
      Polynomial.C (MvPolynomial.X (3 : Fin 4)) := MvPolynomial.finSuccEquiv_X_succ (j := 3)
  have h : (MvPolynomial.finSuccEquiv K 4).toAlgHom.comp (substitute (K := K)) =
      (SecondJetLocal.contact (K := K)).comp (flatEquiv (K := K)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [substitute, SecondJetSupport.flatEquiv_X, SecondJetLocal.baseEval,
        h0, h1, h2, h3, h4] <;> ring
  exact DFunLike.congr_fun h P

end
end ProximityPrize.SubmissionLower.SecondJetDifferentiation

end Compact_SecondJetDifferentiation
