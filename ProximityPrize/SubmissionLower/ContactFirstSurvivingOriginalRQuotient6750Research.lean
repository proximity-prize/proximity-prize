import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFirstSurvivingDerivativeProduct6700Research
import ProximityPrize.SubmissionLower.ContactTranslation

 









namespace ProximityPrize.SubmissionLower
namespace ContactFirstSurvivingOriginalRQuotient6750Research

open scoped Classical
open ContactFirstSurvivingDerivativeProduct6700Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K : Type*} [Field K]

abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

theorem quotient_specializes_zero_of_first_surviving_R
    (G Q : Poly4 K) (P : Polynomial K) (gamma : K) (k : Nat)
    (hlower : ∀ i < k,
      ContactTranslation.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[i] G) = 0)
    (hproduct : ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[k] (G * Q)) = 0)
    (hsurvives : ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[k] G) ≠ 0) :
    ContactTranslation.specialization K P gamma Q = 0 := by
  let D : Derivation K (Poly4 K) (Poly4 K) := MvPolynomial.pderiv (2 : Fin 4)
  let value : Poly4 K →+* Polynomial K :=
    (ContactTranslation.specialization K P gamma).toRingHom
  have hformula := map_iterate_product_at_first_survival
    D value G Q k 0
    (by simpa [D, value] using hlower)
    (by intro i hi; omega)
  have hformula' :
      ContactTranslation.specialization K P gamma
          ((MvPolynomial.pderiv (2 : Fin 4))^[k] (G * Q)) =
        ContactTranslation.specialization K P gamma
            ((MvPolynomial.pderiv (2 : Fin 4))^[k] G) *
          ContactTranslation.specialization K P gamma Q := by
    simpa [D, value] using hformula
  have hmul :
      ContactTranslation.specialization K P gamma
          ((MvPolynomial.pderiv (2 : Fin 4))^[k] G) *
        ContactTranslation.specialization K P gamma Q = 0 := by
    rw [← hformula']
    exact hproduct
  exact (mul_eq_zero.mp hmul).resolve_left hsurvives

 



theorem terminal_R_or_quotient_specializes_zero
    (G Q : Poly4 K) (P : Polynomial K) (gamma : K) (j : Nat)
    (hproducts : ∀ k ≤ j,
      ContactTranslation.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[k] (G * Q)) = 0) :
    ContactTranslation.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[j] G) = 0 ∨
      ContactTranslation.specialization K P gamma Q = 0 := by
  classical
  by_cases hj : ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[j] G) = 0
  · exact Or.inl hj
  · right
    let survives : Nat → Prop := fun k ↦
      k ≤ j ∧ ContactTranslation.specialization K P gamma
        ((MvPolynomial.pderiv (2 : Fin 4))^[k] G) ≠ 0
    have hex : ∃ k, survives k := ⟨j, le_rfl, hj⟩
    let k := Nat.find hex
    have hk : survives k := Nat.find_spec hex
    have hlower : ∀ i < k,
        ContactTranslation.specialization K P gamma
          ((MvPolynomial.pderiv (2 : Fin 4))^[i] G) = 0 := by
      intro i hik
      by_contra hi
      have hij : i ≤ j := (Nat.le_of_lt hik).trans hk.1
      have hki : k ≤ i := Nat.find_min' hex ⟨hij, hi⟩
      omega
    exact quotient_specializes_zero_of_first_surviving_R G Q P gamma k
      hlower (hproducts k hk.1) hk.2

end

end ContactFirstSurvivingOriginalRQuotient6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFirstSurvivingOriginalRQuotient6750Research.quotient_specializes_zero_of_first_surviving_R
#print axioms ProximityPrize.SubmissionLower.ContactFirstSurvivingOriginalRQuotient6750Research.terminal_R_or_quotient_specializes_zero
