import ProximityPrize.SubmissionLower.ContactTaylorNumerators

namespace ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra

open ContactDifferentialRing ContactTaylorNumerators DifferentialTaylorCoefficients

noncomputable section

section Algebra

variable {K : Type*} [CommRing K]

def horizontalDerivation : Derivation K (Poly4 K) (Poly4 K) :=
  MvPolynomial.pderiv (0 : Fin 4) +
    (MvPolynomial.X (2 : Fin 4) : Poly4 K) • MvPolynomial.pderiv (1 : Fin 4)

def baseDerivation (F : Poly4 K) : Derivation K (Poly4 K) (Poly4 K) :=
  polyH K F • horizontalDerivation + polyG K F • MvPolynomial.pderiv (2 : Fin 4)

theorem baseDerivation_apply (F P : Poly4 K) :
    baseDerivation F P = polyH K F *
      (MvPolynomial.pderiv (0 : Fin 4) P +
        MvPolynomial.X (2 : Fin 4) * MvPolynomial.pderiv (1 : Fin 4) P) +
      polyG K F * MvPolynomial.pderiv (2 : Fin 4) P := by
  simp only [baseDerivation, horizontalDerivation, Derivation.add_apply,
    Derivation.smul_apply, smul_eq_mul]

theorem numeratorStep_eq (F P : Poly4 K) (b : ℕ) :
    numeratorStep K F b P = polyH K F * baseDerivation F P -
      (2 * b : ℕ) * P * baseDerivation F (polyH K F) := by
  simp only [numeratorStep, clearedStep, baseDerivation_apply]
  ring

theorem numerator_one (F : Poly4 K) :
    numerator K F 1 = MvPolynomial.X (2 : Fin 4) * polyH K F ^ 2 := by
  simp [numerator, numeratorStep, clearedStep, MvPolynomial.pderiv_X]

theorem baseDerivation_R (F : Poly4 K) :
    baseDerivation F (MvPolynomial.X (2 : Fin 4)) = polyG K F := by
  simp [baseDerivation_apply, MvPolynomial.pderiv_X]

theorem numerator_two (F : Poly4 K) :
    numerator K F 2 = polyH K F ^ 3 * polyG K F := by
  rw [numerator_succ, numerator_one, numeratorStep_eq, leibniz_product,
    baseDerivation_R, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, Nat.cast_ofNat]
  ring

def baseNumerator (F : Poly4 K) : ℕ → Poly4 K
  | 0 => polyG K F
  | n + 1 => polyH K F * baseDerivation F (baseNumerator F n) -
      (2 * n + 1 : ℕ) * baseNumerator F n * baseDerivation F (polyH K F)

theorem numeratorStep_H_cube (F P : Poly4 K) (n : ℕ) :
    numeratorStep K F (n + 2) (polyH K F ^ 3 * P) =
      polyH K F ^ 3 * (polyH K F * baseDerivation F P -
        (2 * n + 1 : ℕ) * P * baseDerivation F (polyH K F)) := by
  rw [numeratorStep_eq, leibniz_product, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem numerator_eq_H_cube (F : Poly4 K) (n : ℕ) :
    numerator K F (n + 2) = polyH K F ^ 3 * baseNumerator F n := by
  induction n with
  | zero => exact numerator_two F
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, numerator_succ, ih,
      numeratorStep_H_cube]
    rfl

end Algebra

section Agreement

variable {K : Type*} [Field K]

end Agreement

end

end ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra
