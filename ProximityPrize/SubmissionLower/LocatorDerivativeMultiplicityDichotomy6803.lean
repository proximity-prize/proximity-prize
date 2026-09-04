import ProximityPrize.SubmissionLower.LocatorDerivativeWeightDescent6803

/-!
# Coprime-or-repeated dichotomy for derivative-chain components

Let `C` be an irreducible positive-`R` component of `pderiv R G`.  In
characteristic larger than its `R`-degree, either `C` is coprime to the
predecessor `G`, or `C^2` divides `G`.  This is the algebraic half of the
finite-geometry/curve-incidence split used by the 68.03 chain target.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeMultiplicityDichotomy6803

open RCN081 RCN267 RCN313

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

/-- A common irreducible factor of a polynomial and its `R` derivative occurs
at least twice in the polynomial. -/
theorem sq_dvd_of_dvd_pderiv
    (C G : MvPolynomial (Fin 4) K) (hC : Irreducible C)
    (p : ℕ) [CharP K p] (hpos : 0 < C.degreeOf (2 : Fin 4))
    (hsmall : C.degreeOf (2 : Fin 4) < p)
    (hCG : C ∣ G)
    (hCdG : C ∣ MvPolynomial.pderiv (2 : Fin 4) G) :
    C ^ 2 ∣ G := by
  obtain ⟨H, rfl⟩ := hCG
  have hdCne : MvPolynomial.pderiv (2 : Fin 4) C ≠ 0 :=
    R_derivative_nonzero C p hpos hsmall
  have hnot : ¬ C ∣ MvPolynomial.pderiv (2 : Fin 4) C := by
    intro hdiv
    have hle := degreeOf_le_of_dvd (2 : Fin 4) C
      (MvPolynomial.pderiv (2 : Fin 4) C) hdiv hdCne
    have hdrop := pderiv_same_degree_bound (2 : Fin 4) C
      (C.degreeOf (2 : Fin 4)) le_rfl
    omega
  have hprod : C ∣ MvPolynomial.pderiv (2 : Fin 4) C * H := by
    have hmultiple : C ∣ C * MvPolynomial.pderiv (2 : Fin 4) H :=
      dvd_mul_right C _
    have hsub := dvd_sub hCdG hmultiple
    simpa only [MvPolynomial.pderiv_mul, add_sub_cancel_right] using hsub
  have hCH : C ∣ H := (hC.prime.dvd_mul.mp hprod).resolve_left hnot
  obtain ⟨T, rfl⟩ := hCH
  exact ⟨T, by simp only [pow_two, mul_assoc]⟩

/-- Every irreducible positive-`R` component of a derivative is either proper
over the predecessor or consumes two copies of the predecessor's factor
budget. -/
theorem isRelPrime_predecessor_or_sq_dvd
    (C G : MvPolynomial (Fin 4) K) (hC : Irreducible C)
    (p : ℕ) [CharP K p] (hpos : 0 < C.degreeOf (2 : Fin 4))
    (hsmall : C.degreeOf (2 : Fin 4) < p)
    (hCdG : C ∣ MvPolynomial.pderiv (2 : Fin 4) G) :
    IsRelPrime C G ∨ C ^ 2 ∣ G := by
  by_cases hCG : C ∣ G
  · exact Or.inr (sq_dvd_of_dvd_pderiv C G hC p hpos hsmall hCG hCdG)
  · exact Or.inl (hC.isRelPrime_iff_not_dvd.mpr hCG)

end

end ProximityPrize.SubmissionLower.LocatorDerivativeMultiplicityDichotomy6803
