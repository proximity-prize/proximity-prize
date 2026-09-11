import ProximityPrize.SubmissionLower.Part.G031


section Compact_SecondJetGlobalDifferentiation
/-! Support and local-contact behavior of global S derivatives. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

theorem support_pderiv (P : Poly (K := K)) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ (pderiv 1 P).support) : d+Finsupp.single 1 1 ∈ P.support := by
  have h := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact h (by rw [hz, zero_mul])

theorem support_iterate (P : Poly (K := K)) (n : ℕ) (d : Fin 5 →₀ ℕ)
    (hd : d ∈ ((pderiv 1)^[n] P).support) : d+Finsupp.single 1 n ∈ P.support := by
  induction n generalizing d with
  | zero => simpa using hd
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hd
    have hh := ih (d+Finsupp.single 1 1) (support_pderiv _ d hd)
    have he : d+Finsupp.single 1 1+Finsupp.single 1 n = d+Finsupp.single 1 (n+1) := by
      rw [add_assoc, ← Finsupp.single_add, Nat.add_comm 1 n]
    rwa [he] at hh

theorem localize_pderiv (x u0 u1 : K) (P : Poly (K := K)) :
    localize x u0 u1 (pderiv 1 P) = pderiv 1 (localize x u0 u1 P) := by
  have hX (j : Fin 5) : localize x u0 u1 (pderiv 1 (MvPolynomial.X j)) =
      pderiv 1 (localize x u0 u1 (MvPolynomial.X j)) := by
    fin_cases j <;> simp [localize, pderiv_mul, Pi.single_apply]
  induction P using MvPolynomial.induction_on with
  | C c => simp [localize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP => simp only [pderiv_mul, map_add, map_mul, hP, hX]

theorem localize_iterate (x u0 u1 : K) (P : Poly (K := K)) (n : ℕ) :
    localize x u0 u1 ((pderiv 1)^[n] P) = (pderiv 1)^[n] (localize x u0 u1 P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', localize_pderiv, ih]

theorem local_derivative_contact (x u0 u1 : K) (P : Poly (K := K)) (m d : ℕ)
    (hP : MvPolynomial.X 0^(m+d) ∣ substitute (K := K) (localize x u0 u1 P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) (localize x u0 u1 ((pderiv 1)^[d] P)) := by
  rw [localize_iterate]
  exact iterate_derivative_contact (localize x u0 u1 P) m d hP

theorem nested_to_flat_contact (P : Poly (K := K)) (m : ℕ)
    (hP : Polynomial.X^m ∣ SecondJetLocal.contact (K := K) (flatEquiv (K := K) P)) :
    MvPolynomial.X 0^m ∣ substitute (K := K) P := by
  obtain ⟨Q,hQ⟩ := hP
  refine ⟨(MvPolynomial.finSuccEquiv K 4).symm Q,?_⟩
  apply (MvPolynomial.finSuccEquiv K 4).injective
  rw [substitute_contact, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    AlgEquiv.apply_symm_apply]
  exact hQ


end
end ProximityPrize.SubmissionLower.SecondJetGlobalDifferentiation

end Compact_SecondJetGlobalDifferentiation
