import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

/-!
# Agreement-rooted tangency

This module isolates the formal chain-rule step used by the ramified
score-64 route.  A bivariate relation is viewed as a polynomial in `Y`
whose coefficients are polynomials in `X`.  If a polynomial section is an
exact root and the `Y`-derivative vanishes at an agreement point, then the
coefficientwise `X`-derivative vanishes there as well.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

variable {F : Type} [Field F]

/-- Formal partial derivative in the coefficient variable `X`. -/
noncomputable def coeffDerivativeX (B : F[X][Y]) : F[X][Y] :=
  B.sum fun j c => Polynomial.monomial j c.derivative

@[simp]
theorem coeffDerivativeX_add (B C : F[X][Y]) :
    coeffDerivativeX (B + C) = coeffDerivativeX B + coeffDerivativeX C := by
  classical
  unfold coeffDerivativeX
  apply Polynomial.sum_add_index
  · intro i
    simp
  · intro i a b
    simp

@[simp]
theorem coeffDerivativeX_monomial (n : ℕ) (c : F[X]) :
    coeffDerivativeX (Polynomial.monomial n c) =
      Polynomial.monomial n c.derivative := by
  classical
  simp [coeffDerivativeX]

@[simp]
theorem coeffDerivativeX_derivative (B : F[X][Y]) :
    coeffDerivativeX B.derivative = (coeffDerivativeX B).derivative := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC => simp [hB, hC]
  | monomial n c =>
      simp only [Polynomial.derivative_monomial, coeffDerivativeX_monomial]
      simp [Polynomial.derivative_mul]

/-- Algebraic chain rule for a bivariate polynomial with both its
coefficient variable and its root variable depending on `X`. -/
theorem derivative_eval_eq_coeffDerivativeX_add
    (B : F[X][Y]) (P : F[X]) :
    (B.eval P).derivative =
      (coeffDerivativeX B).eval P + B.derivative.eval P * P.derivative := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC =>
      simp only [Polynomial.eval_add, Polynomial.derivative_add,
        coeffDerivativeX_add, hB, hC]
      ring
  | monomial n c =>
      simp only [Polynomial.eval_monomial, coeffDerivativeX_monomial,
        Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rw [Polynomial.C_eq_natCast]
      ring

private theorem eval_eval_eq_eval₂
    (B : F[X][Y]) (P : F[X]) (x : F) :
    (B.eval P).eval x =
      Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x) B := by
  have h := Polynomial.hom_eval₂ B (RingHom.id F[X])
    (Polynomial.evalRingHom x) P
  simpa using h

/-- Pointwise chain rule. -/
theorem eval_coeffDerivativeX_add_yDerivative
    (B : F[X][Y]) (P : F[X]) (x : F) :
    (B.eval P).derivative.eval x =
      Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
          (coeffDerivativeX B) +
        Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
          B.derivative * P.derivative.eval x := by
  rw [derivative_eval_eq_coeffDerivativeX_add]
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  rw [eval_eval_eq_eval₂, eval_eval_eq_eval₂]

/-- Second-order algebraic chain rule.  This is the formal identity behind
the slope equation at a ramified agreement point. -/
theorem derivative_derivative_eval_eq
    (B : F[X][Y]) (P : F[X]) :
    (B.eval P).derivative.derivative =
      (coeffDerivativeX (coeffDerivativeX B)).eval P +
        2 *
          ((coeffDerivativeX B).derivative.eval P * P.derivative) +
        B.derivative.derivative.eval P * P.derivative ^ 2 +
        B.derivative.eval P * P.derivative.derivative := by
  rw [derivative_eval_eq_coeffDerivativeX_add]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul]
  rw [derivative_eval_eq_coeffDerivativeX_add,
    derivative_eval_eq_coeffDerivativeX_add]
  simp only [coeffDerivativeX_derivative]
  ring

/-- Pointwise second-order chain rule. -/
theorem eval_second_chain
    (B : F[X][Y]) (P : F[X]) (x : F) :
    (B.eval P).derivative.derivative.eval x =
      Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
          (coeffDerivativeX (coeffDerivativeX B)) +
        2 *
          (Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
              (coeffDerivativeX B).derivative * P.derivative.eval x) +
        Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
            B.derivative.derivative * (P.derivative.eval x) ^ 2 +
        Polynomial.eval₂ (Polynomial.evalRingHom x) (P.eval x)
            B.derivative * P.derivative.derivative.eval x := by
  rw [derivative_derivative_eval_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow]
  rw [eval_eval_eq_eval₂, eval_eval_eq_eval₂,
    eval_eval_eq_eval₂, eval_eval_eq_eval₂]

/-- At a multiplicity-at-least-three agreement point, the witness slope is
rational whenever the mixed partial is nonzero.  This is the first
nontrivial endpoint of the agreement-rooted ramification route. -/
theorem slope_eq_neg_div_of_exact_root_of_third_order_ramification
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hExact : B.eval P = 0)
    (hagree : P.eval x = y)
    (hY : Polynomial.eval₂ (Polynomial.evalRingHom x) y
      B.derivative = 0)
    (hYY : Polynomial.eval₂ (Polynomial.evalRingHom x) y
      B.derivative.derivative = 0)
    (hXY : Polynomial.eval₂ (Polynomial.evalRingHom x) y
      (coeffDerivativeX B).derivative ≠ 0)
    (htwo : (2 : F) ≠ 0) :
    P.derivative.eval x =
      -Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX (coeffDerivativeX B)) /
        (2 * Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX B).derivative) := by
  have htotal : (B.eval P).derivative.derivative.eval x = 0 := by
    rw [hExact]
    simp
  rw [eval_second_chain B P x, hagree, hY, hYY,
    zero_mul, add_zero] at htotal
  have hden :
      (2 : F) * Polynomial.eval₂ (Polynomial.evalRingHom x) y
        (coeffDerivativeX B).derivative ≠ 0 :=
    mul_ne_zero htwo hXY
  apply (eq_div_iff hden).2
  linear_combination htotal

/-- Ramified agreement forces tangency in the coefficient variable.

The premise `hY` is exactly the repeated-root condition after specializing
at `(x,y)`.  The conclusion is the formal `R_X(x,y)=0` statement. -/
theorem coeffDerivativeX_eval_eq_zero_of_exact_root_of_yDerivative_eq_zero
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hExact : B.eval P = 0)
    (hagree : P.eval x = y)
    (hY : Polynomial.eval₂ (Polynomial.evalRingHom x) y B.derivative = 0) :
    Polynomial.eval₂ (Polynomial.evalRingHom x) y (coeffDerivativeX B) = 0 := by
  have htotal : (B.eval P).derivative.eval x = 0 := by
    rw [hExact]
    simp
  rw [eval_coeffDerivativeX_add_yDerivative B P x, hagree, hY,
    zero_mul, add_zero] at htotal
  exact htotal

/-- Divisibility by the square of the agreement section supplies the
repeated-root premise used by the tangency theorem. -/
theorem coeffDerivativeX_eval_eq_zero_of_exact_root_of_sq_dvd
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hExact : B.eval P = 0)
    (hagree : P.eval x = y)
    (hsq : (Polynomial.X - Polynomial.C y) ^ 2 ∣
      B.map (Polynomial.evalRingHom x)) :
    Polynomial.eval₂ (Polynomial.evalRingHom x) y (coeffDerivativeX B) = 0 := by
  apply coeffDerivativeX_eval_eq_zero_of_exact_root_of_yDerivative_eq_zero
    B P x y hExact hagree
  rw [Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map]
  obtain ⟨C, hC⟩ := hsq
  have hfactor :
      ((Polynomial.X - Polynomial.C y) ^ 2 : F[X]).eval y = 0 := by
    simp
  have hfactorDerivative :
      ((Polynomial.X - Polynomial.C y) ^ 2 : F[X]).derivative.eval y = 0 := by
    rw [Polynomial.derivative_pow]
    simp
  rw [hC, Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul, hfactor, hfactorDerivative]
  ring

private theorem eval_derivative_eq_zero_of_cube_dvd
    (S : F[X]) (y : F)
    (hcube : (Polynomial.X - Polynomial.C y) ^ 3 ∣ S) :
    S.derivative.eval y = 0 := by
  obtain ⟨C, rfl⟩ := hcube
  rw [Polynomial.derivative_mul, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul]
  simp [Polynomial.derivative_pow]

private theorem eval_secondDerivative_eq_zero_of_cube_dvd
    (S : F[X]) (y : F)
    (hcube : (Polynomial.X - Polynomial.C y) ^ 3 ∣ S) :
    S.derivative.derivative.eval y = 0 := by
  obtain ⟨C, rfl⟩ := hcube
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.eval_add, Polynomial.eval_mul]
  have h0 : ((Polynomial.X - Polynomial.C y) ^ 3 : F[X]).eval y = 0 := by
    simp
  have h1 : ((Polynomial.X - Polynomial.C y) ^ 3 : F[X]).derivative.eval y = 0 := by
    simp [Polynomial.derivative_pow]
  have h2 :
      ((Polynomial.X - Polynomial.C y) ^ 3 : F[X]).derivative.derivative.eval y = 0 := by
    simp [Polynomial.derivative_pow, Polynomial.derivative_mul]
  rw [h0, h1, h2]
  ring

/-- Cubic divisibility supplies the two vanishing `Y`-partials required by
the rational-slope theorem. -/
theorem slope_eq_neg_div_of_exact_root_of_cube_dvd
    (B : F[X][Y]) (P : F[X]) (x y : F)
    (hExact : B.eval P = 0)
    (hagree : P.eval x = y)
    (hcube : (Polynomial.X - Polynomial.C y) ^ 3 ∣
      B.map (Polynomial.evalRingHom x))
    (hXY : Polynomial.eval₂ (Polynomial.evalRingHom x) y
      (coeffDerivativeX B).derivative ≠ 0)
    (htwo : (2 : F) ≠ 0) :
    P.derivative.eval x =
      -Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX (coeffDerivativeX B)) /
        (2 * Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX B).derivative) := by
  apply slope_eq_neg_div_of_exact_root_of_third_order_ramification
    B P x y hExact hagree
  · rw [Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map]
    exact eval_derivative_eq_zero_of_cube_dvd _ y hcube
  · rw [Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map,
      ← Polynomial.derivative_map]
    exact eval_secondDerivative_eq_zero_of_cube_dvd _ y hcube
  · exact hXY
  · exact htwo

/-- Benchmark-facing trivariate wrapper for agreement-rooted tangency. -/
theorem tri_coeffDerivativeX_eval_eq_zero_of_sq_dvd
    (R : F[X][X][Y]) (P : F[X]) (z x y : F)
    (hExact : triEval R z P = 0)
    (hagree : P.eval x = y)
    (hsq : (Polynomial.X - Polynomial.C y) ^ 2 ∣
      (triSpecializeZ R z).map (Polynomial.evalRingHom x)) :
    Polynomial.eval₂ (Polynomial.evalRingHom x) y
      (coeffDerivativeX (triSpecializeZ R z)) = 0 := by
  apply coeffDerivativeX_eval_eq_zero_of_exact_root_of_sq_dvd
    (triSpecializeZ R z) P x y
  · simpa only [← triEval_eq_eval_triSpecializeZ] using hExact
  · exact hagree
  · exact hsq

/-- Benchmark-facing trivariate wrapper for the multiplicity-three rational
slope formula. -/
theorem tri_slope_eq_neg_div_of_cube_dvd
    (R : F[X][X][Y]) (P : F[X]) (z x y : F)
    (hExact : triEval R z P = 0)
    (hagree : P.eval x = y)
    (hcube : (Polynomial.X - Polynomial.C y) ^ 3 ∣
      (triSpecializeZ R z).map (Polynomial.evalRingHom x))
    (hXY : Polynomial.eval₂ (Polynomial.evalRingHom x) y
      (coeffDerivativeX (triSpecializeZ R z)).derivative ≠ 0)
    (htwo : (2 : F) ≠ 0) :
    P.derivative.eval x =
      -Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX
            (coeffDerivativeX (triSpecializeZ R z))) /
        (2 * Polynomial.eval₂ (Polynomial.evalRingHom x) y
          (coeffDerivativeX (triSpecializeZ R z)).derivative) := by
  apply slope_eq_neg_div_of_exact_root_of_cube_dvd
    (triSpecializeZ R z) P x y
  · simpa only [← triEval_eq_eval_triSpecializeZ] using hExact
  · exact hagree
  · exact hcube
  · exact hXY
  · exact htwo

end ProximityPrize.SubmissionLower
