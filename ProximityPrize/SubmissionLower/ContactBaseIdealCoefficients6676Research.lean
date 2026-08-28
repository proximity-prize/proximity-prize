import ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra6676Research

/-! .




 -/

namespace ProximityPrize.SubmissionLower.ContactBaseIdealCoefficients6676Research

open ContactDifferentialRing ContactTaylorNumerators DifferentialTaylorCoefficients
open ContactBaseIdealAlgebra6676Research

noncomputable section

variable {K : Type*} [CommRing K]

def sameContribution (F : Poly4 K) (n j : ℕ) (P : Poly4 K) : Poly4 K :=
  polyH K F * horizontalDerivation P -
    (n + j : ℕ) * P * horizontalDerivation (polyH K F) +
      (j : ℕ) * P * MvPolynomial.pderiv (2 : Fin 4) (polyG K F)

def downContribution (F : Poly4 K) (j : ℕ) (P : Poly4 K) : Poly4 K :=
  (j : ℕ) * P * horizontalDerivation (polyG K F)

def upContribution (F : Poly4 K) (n j : ℕ) (P : Poly4 K) : Poly4 K :=
  polyH K F * MvPolynomial.pderiv (2 : Fin 4) P -
    (n + j : ℕ) * P * MvPolynomial.pderiv (2 : Fin 4) (polyH K F)

def baseMonomial (F : Poly4 K) (k j : ℕ) (P : Poly4 K) : Poly4 K :=
  polyH K F ^ (k - j) * polyG K F ^ j * P

def baseStep (F : Poly4 K) (n : ℕ) (P : Poly4 K) : Poly4 K :=
  polyH K F * baseDerivation F P -
    (2 * n + 1 : ℕ) * P * baseDerivation F (polyH K F)

/-- . -/
theorem baseStep_monomial (F P : Poly4 K) (n j : ℕ) (hj : j ≤ n + 1) :
    baseStep F n (baseMonomial F (n + 1) j P) =
      baseMonomial F (n + 2) j (sameContribution F n j P) +
      baseMonomial F (n + 2) (j - 1) (downContribution F j P) +
      baseMonomial F (n + 2) (j + 1) (upContribution F n j P) := by
  cases j with
  | zero =>
    have he : n + 2 - 1 = n + 1 := by omega
    simp only [baseStep, baseMonomial, sameContribution, downContribution,
      upContribution, baseDerivation, Derivation.add_apply, Derivation.smul_apply,
      smul_eq_mul, Nat.sub_zero, Nat.zero_sub, Nat.cast_zero, zero_mul, mul_zero,
      pow_zero, mul_one, Nat.zero_add, he, add_zero, leibniz_product,
      Derivation.leibniz_pow, nsmul_eq_mul, Nat.add_sub_cancel]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    ring
  | succ j =>
    by_cases ht : j = n
    · subst j
      simp only [baseStep, baseMonomial, sameContribution, downContribution,
        upContribution, baseDerivation, Derivation.add_apply, Derivation.smul_apply,
        smul_eq_mul, Nat.add_sub_add_left, Nat.add_sub_cancel, Nat.sub_self,
        Nat.reduceSub, Nat.add_sub_cancel_left, pow_zero, one_mul,
        leibniz_product, Derivation.leibniz_pow, nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
      ring
    · have hjn : j + 1 ≤ n := by omega
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hjn
      subst n
      have e₁ : j + 1 + u + 1 - (j + 1) = u + 1 := by omega
      have e₂ : j + 1 + u + 2 - (j + 1) = u + 2 := by omega
      have e₃ : j + 1 + u + 2 - j = u + 3 := by omega
      have e₄ : j + 1 + u + 2 - (j + 1 + 1) = u + 1 := by omega
      simp only [baseStep, baseMonomial, sameContribution, downContribution,
        upContribution, baseDerivation, Derivation.add_apply, Derivation.smul_apply,
        smul_eq_mul, Nat.add_sub_cancel, e₁, e₂, e₃, e₄,
        leibniz_product, Derivation.leibniz_pow, nsmul_eq_mul]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
      ring

def coefficientStep (F : Poly4 K) (n : ℕ) (C : ℕ → Poly4 K) (j : ℕ) : Poly4 K :=
  sameContribution F n j (C j) + downContribution F (j + 1) (C (j + 1)) +
    if j = 0 then 0 else upContribution F n (j - 1) (C (j - 1))

def baseCoefficients (F : Poly4 K) : ℕ → ℕ → Poly4 K
  | 0, j => if j = 1 then 1 else 0
  | n + 1, j => coefficientStep F n (baseCoefficients F n) j

theorem baseCoefficients_zero (F : Poly4 K) (n j : ℕ) (hj : n + 1 < j) :
    baseCoefficients F n j = 0 := by
  induction n generalizing j with
  | zero => simp [baseCoefficients, show j ≠ 1 by omega]
  | succ n ih =>
    simp [baseCoefficients, coefficientStep, ih j (by omega),
      ih (j + 1) (by omega), ih (j - 1) (by omega),
      sameContribution, downContribution, upContribution]

theorem baseStep_sum (F : Poly4 K) (n : ℕ) (s : Finset ℕ) (P : ℕ → Poly4 K) :
    baseStep F n (∑ j ∈ s, P j) = ∑ j ∈ s, baseStep F n (P j) := by
  simp only [baseStep, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem coefficientStep_represents (F : Poly4 K) (n : ℕ) (C : ℕ → Poly4 K)
    (hC : ∀ j, n + 1 < j → C j = 0) :
    baseStep F n (∑ j ∈ Finset.range (n + 2), baseMonomial F (n + 1) j (C j)) =
      ∑ j ∈ Finset.range (n + 3), baseMonomial F (n + 2) j (coefficientStep F n C j) := by
  let a j := baseMonomial F (n + 2) j (sameContribution F n j (C j))
  let b j := baseMonomial F (n + 2) (j - 1) (downContribution F j (C j))
  let c j := baseMonomial F (n + 2) (j + 1) (upContribution F n j (C j))
  have ha : (∑ j ∈ Finset.range (n + 2), a j) = ∑ j ∈ Finset.range (n + 3), a j := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp [a, hC (n + 2) (by omega), sameContribution, baseMonomial]
  have hb0 : b 0 = 0 := by simp [b, downContribution, baseMonomial]
  have hb2 : b (n + 2) = 0 := by
    simp [b, hC (n + 2) (by omega), downContribution, baseMonomial]
  have hb3 : b (n + 3) = 0 := by
    simp [b, hC (n + 3) (by omega), downContribution, baseMonomial]
  have hb : (∑ j ∈ Finset.range (n + 2), b j) =
      ∑ j ∈ Finset.range (n + 3), b (j + 1) := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1), b (j + 1) := by
        rw [Finset.sum_range_succ']
        simp only [hb0, add_zero]
      _ = _ := by
        symm
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [show n + 1 + 1 = n + 2 by omega, show n + 2 + 1 = n + 3 by omega,
          hb2, hb3, add_zero]
  have hc : (∑ j ∈ Finset.range (n + 2), c j) =
      ∑ j ∈ Finset.range (n + 3), baseMonomial F (n + 2) j
        (if j = 0 then 0 else upContribution F n (j - 1) (C (j - 1))) := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, baseMonomial, mul_zero, add_zero]
    rfl
  rw [baseStep_sum]
  calc
    _ = ∑ j ∈ Finset.range (n + 2), (a j + b j + c j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact baseStep_monomial F (C j) n j (by have := Finset.mem_range.mp hj; omega)
    _ = (∑ j ∈ Finset.range (n + 2), a j) +
        (∑ j ∈ Finset.range (n + 2), b j) + (∑ j ∈ Finset.range (n + 2), c j) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [ha, hb, hc]
      simp only [a, b, coefficientStep, baseMonomial, mul_add,
        Finset.sum_add_distrib, Nat.add_sub_cancel]

/-- . -/
theorem baseNumerator_eq_sum (F : Poly4 K) (n : ℕ) :
    baseNumerator F n =
      ∑ j ∈ Finset.range (n + 2), baseMonomial F (n + 1) j (baseCoefficients F n j) := by
  induction n with
  | zero => simp [baseNumerator, baseCoefficients, baseMonomial]
  | succ n ih =>
    change baseStep F n (baseNumerator F n) = _
    rw [ih, coefficientStep_represents F n _ (baseCoefficients_zero F n)]
    rfl

theorem numerator_eq_coefficient_sum (F : Poly4 K) (n : ℕ) :
    numerator K F (n + 2) = polyH K F ^ 3 *
      ∑ j ∈ Finset.range (n + 2),
        polyH K F ^ (n + 1 - j) * polyG K F ^ j * baseCoefficients F n j := by
  rw [numerator_eq_H_cube, baseNumerator_eq_sum]
  rfl

end

end ProximityPrize.SubmissionLower.ContactBaseIdealCoefficients6676Research
