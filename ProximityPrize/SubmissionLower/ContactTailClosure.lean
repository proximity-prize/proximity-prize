import ProximityPrize.SubmissionLower.ContactAgreementEvaluation
import ProximityPrize.SubmissionLower.ContactGlobalPolynomiality

namespace ProximityPrize.SubmissionLower.ContactTailClosure

open ContactDifferentialRing ContactTaylorNumerators ContactAgreementEvaluation
open ContactRegularPoint ContactPolynomiality ContactGlobalPolynomiality
open DifferentialTaylorCoefficients
open ContactInterpolation ContactTranslation

noncomputable section

variable (K : Type*) [CommRing K]

theorem numeratorStep_mul_equation (F A : Poly4 K) (b : ℕ) :
    numeratorStep K F b (F * A) = F * numeratorStep K F b A := by
  unfold numeratorStep clearedStep
  simp only [leibniz_product]
  unfold polyG polyH
  ring

theorem equation_dvd_numeratorStep (F M : Poly4 K) (b : ℕ) (h : F ∣ M) :
    F ∣ numeratorStep K F b M := by
  rcases h with ⟨A, rfl⟩
  rw [numeratorStep_mul_equation]
  exact dvd_mul_right F _

theorem equation_dvd_all_later_numerators (F : Poly4 K) (b : ℕ)
    (h : F ∣ numerator K F b) :
    ∀ j, b ≤ j → F ∣ numerator K F j := by
  intro j hbj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbj
  clear hbj
  induction d with
  | zero => simpa using h
  | succ d ih =>
      simpa only [Nat.add_succ, numerator_succ] using
        equation_dvd_numeratorStep K F (numerator K F (b + d)) (b + d) ih

variable {L : Type*} [CommRing L]

theorem all_later_numerators_vanish (coefficients : K →+* L)
    (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (b : ℕ) (h : F ∣ numerator K F b) :
    ∀ j, b ≤ j →
      MvPolynomial.eval₂Hom coefficients v (numerator K F j) = 0 := by
  intro j hbj
  rcases equation_dvd_all_later_numerators K F b h j hbj with ⟨A, hA⟩
  rw [hA, map_mul, hF, zero_mul]

end

section PolynomialFamily

variable {K L : Type*} [Field K] [Field L]

theorem all_tail_jets_zero_of_first_tail_dvd
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hreg : MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (w : ℕ) (hdiv : F ∣ numerator K F (w + 1)) :
    ∀ j, w < j →
      jetCoefficient (contactDerivation K F)
        (regularPointValue coefficients F v hF hreg)
        (contactCoordinate K F (1 : Fin 4)) j = 0 := by
  intro j hj
  rw [jetCoefficient_eq_evaluated_numerator coefficients F v hF hreg]
  rw [all_later_numerators_vanish K coefficients F v hF (w + 1) hdiv j (by omega)]
  simp

end PolynomialFamily

end ProximityPrize.SubmissionLower.ContactTailClosure
