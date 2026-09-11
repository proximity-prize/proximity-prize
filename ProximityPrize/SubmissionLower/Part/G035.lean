import ProximityPrize.SubmissionLower.Part.G034


section Compact_SecondJetSpecialize
/-! From formal second-jet contact to ordinary polynomial root multiplicity. -/
namespace ProximityPrize.SubmissionLower.SecondJetSpecialize
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem hasse_taylor (f : Polynomial K) (x : K) (n : ℕ) :
    Polynomial.hasseDeriv n (Polynomial.taylor x f) =
      Polynomial.taylor x (Polynomial.hasseDeriv n f) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.taylor_coeff, Polynomial.taylor_coeff]
  have hc := congrArg (fun T : Polynomial K →ₗ[K] Polynomial K => (T f).eval x)
    (Polynomial.hasseDeriv_comp (R := K) i n)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.eval_smul,
    nsmul_eq_mul] at hc
  rw [hc]
  simp [Nat.choose_symm_add, mul_comm]

theorem derivative_taylor (f : Polynomial K) (x : K) :
    (Polynomial.taylor x f).derivative = Polynomial.taylor x f.derivative := by
  simpa only [Polynomial.hasseDeriv_one] using hasse_taylor f x 1

def specialize (f : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 f,f,f.derivative,Polynomial.C z]

def realize (q U : Polynomial K) (z : K) : Poly (K := K) →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X,Polynomial.hasseDeriv 2 q,U,q.derivative,Polynomial.C z]

theorem realize_contact (f U : Polynomial K) (x u0 u1 z : K)
    (hagree : f.eval x = u0+u1*z)
    (hU : Polynomial.taylor x f-Polynomial.C (f.eval x) =
      Polynomial.X*((Polynomial.taylor x f).derivative-
        Polynomial.X*Polynomial.hasseDeriv 2 (Polynomial.taylor x f)+Polynomial.X^2*U))
    (P : Poly (K := K)) :
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) =
      Polynomial.taylor x (specialize f z P) := by
  have heq : (realize (Polynomial.taylor x f) U z).comp
      ((substitute (K := K)).comp (localize x u0 u1)) =
      (Polynomial.taylorAlgHom x).comp (specialize f z) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;>
      simp [realize, substitute, localize, specialize, hasse_taylor, derivative_taylor]
    · ring
    · rw [hagree, map_add, map_mul] at hU
      simp only [derivative_taylor, hasse_taylor] at hU
      linear_combination -hU
  exact DFunLike.congr_fun heq P

theorem root_contact (P : Poly (K := K)) (f : Polynomial K) (x u0 u1 z : K) (m : ℕ)
    (hagree : f.eval x = u0+u1*z)
    (hP : MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 P)) :
    (Polynomial.X-Polynomial.C x)^m ∣ specialize f z P := by
  obtain ⟨U,hU⟩ := SecondJetContact.taylor_second_contact f x
  have hd := map_dvd (realize (Polynomial.taylor x f) U z).toRingHom hP
  change realize (Polynomial.taylor x f) U z (MvPolynomial.X 0^m) ∣
    realize (Polynomial.taylor x f) U z (substitute (K := K) (localize x u0 u1 P)) at hd
  rw [map_pow, realize_contact f U x u0 u1 z hagree hU P] at hd
  have hx : realize (Polynomial.taylor x f) U z (MvPolynomial.X 0) = Polynomial.X := by
    simp [realize]
  rw [hx] at hd
  obtain ⟨Q,hQ⟩ := hd
  refine ⟨(Polynomial.taylorEquiv x).symm Q,?_⟩
  apply Polynomial.taylor_injective x
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow]
  have hh : Polynomial.taylor x (Polynomial.X-Polynomial.C x) = Polynomial.X := by simp
  rw [hh]
  change Polynomial.taylor x (specialize f z P) = Polynomial.X^m*
    ((Polynomial.taylorEquiv x) ((Polynomial.taylorEquiv x).symm Q))
  rw [AlgEquiv.apply_symm_apply]
  exact hQ

theorem monomial_degree (f : Polynomial K) (z : K) (w : ℕ) (hf : f.natDegree ≤ w)
    (d : Fin 5 →₀ ℕ) (c : K) :
    (specialize f z (MvPolynomial.monomial d c)).natDegree ≤
      d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (specialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by simp [specialize]
    have h0 : (specialize f z (MvPolynomial.X 0)^d 0).natDegree ≤ d 0 := by simp [specialize]
    have hs : (Polynomial.hasseDeriv 2 f).natDegree ≤ w-2 :=
      (Polynomial.natDegree_hasseDeriv_le f 2).trans (Nat.sub_le_sub_right hf 2)
    have hr : f.derivative.natDegree ≤ w-1 :=
      (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)
    have h1 : (specialize f z (MvPolynomial.X 1)^d 1).natDegree ≤ d 1*(w-2) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 1) hs
    have h2 : (specialize f z (MvPolynomial.X 2)^d 2).natDegree ≤ d 2*w := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 2) hf
    have h3 : (specialize f z (MvPolynomial.X 3)^d 3).natDegree ≤ d 3*(w-1) := by
      simpa [specialize] using Polynomial.natDegree_pow_le_of_le (d 3) hr
    have h4 : (specialize f z (MvPolynomial.X 4)^d 4).natDegree ≤ 0 := by simp [specialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2
        (Polynomial.natDegree_mul_le_of_le h3 h4))))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using hh
  · intro i
    simp

theorem specialization_degree (P : Poly (K := K)) (f : Polynomial K) (z : K) (w D : ℕ)
    (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ d ∈ P.support, d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 < D) :
    (specialize f z P).natDegree < D := by
  classical
  have hterms : ∀ d ∈ P.support,
      (specialize f z (MvPolynomial.monomial d (MvPolynomial.coeff d P))).natDegree ≤ D-1 := by
    intro d hd
    have hw := hP d hd
    have hh := monomial_degree f z w hf d (MvPolynomial.coeff d P)
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun d => specialize f z (MvPolynomial.monomial d (MvPolynomial.coeff d P))) hterms
  exact lt_of_le_of_lt hh (by omega)

end
end ProximityPrize.SubmissionLower.SecondJetSpecialize

end Compact_SecondJetSpecialize
