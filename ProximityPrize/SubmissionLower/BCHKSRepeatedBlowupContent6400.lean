import ProximityPrize.SubmissionLower.BCHKSRepeatedBlowupRelation6400

/-!
# Quadratic content of the repeated-branch blow-up

The singular affine line extracted from the residual score-64 branch supplies
exactly the three identities needed by the generic ramified substitution:
`R = R_X = R_Y = 0`.  This file translates the nested-polynomial notation and
obtains a common `X^2` factor without adding any axiom or interface premise.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

variable {F : Type} [Field F]

/-- Evaluating the outer variable at a constant polynomial and then the
coefficient variable commutes with specializing coefficients first. -/
theorem eval_C_eval_commute
    {A : Type} [CommRing A] (B : A[X][Y]) (x y : A) :
    (B.eval (Polynomial.C y)).eval x =
      (B.map (Polynomial.evalRingHom x)).eval y := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC => simp [hB, hC]
  | monomial n c => simp [Polynomial.map_monomial, Polynomial.eval_monomial]

/-- Because the inserted affine line is constant in the middle variable,
differentiating after insertion is the same as inserting it into the
coefficientwise middle partial. -/
theorem derivative_eval_C_eq_triCoeffDerivativeX_eval
    (R : F[X][X][Y]) (L : F[X]) :
    (R.eval (Polynomial.C L)).derivative =
      (triCoeffDerivativeX R).eval (Polynomial.C L) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS => simp [hR, hS]
  | monomial n c =>
      rw [triCoeffDerivativeX_monomial]
      simp only [Polynomial.eval_monomial, Polynomial.derivative_mul,
        Polynomial.derivative_pow, Polynomial.derivative_C, mul_zero,
        add_zero]

/-- The three singular-line identities imply common quadratic content in the
actual trivariate repeated-branch transform.  The new variables are, from
inside out, the original challenge `Z`, centered coordinate `X`, and slope
coordinate `W`. -/
theorem C_X_sq_dvd_repeated_ramifiedSubstitute
    (R : F[X][X][Y]) (x a b : F)
    (hroot : directAffineObstruction R x a b = 0)
    (hY : (triSpecializeX R x).derivative.eval
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0)
    (hX : directAffineObstruction (triCoeffDerivativeX R) x a b = 0) :
    Polynomial.C (Polynomial.X ^ 2) ∣
      ramifiedSubstitute R (Polynomial.C x)
        (Polynomial.C a + Polynomial.X * Polynomial.C b) := by
  let L : F[X] := Polynomial.C a + Polynomial.X * Polynomial.C b
  have hzero :
      (R.eval (Polynomial.C L)).eval (Polynomial.C x) = 0 := by
    rw [eval_C_eval_commute]
    simpa only [L, directAffineObstruction, fixedAffineOwnerObstruction,
      triSpecializeX] using hroot
  have hmiddleRaw :
      ((triCoeffDerivativeX R).eval (Polynomial.C L)).eval
        (Polynomial.C x) = 0 := by
    rw [eval_C_eval_commute]
    simpa only [L, directAffineObstruction, fixedAffineOwnerObstruction,
      triSpecializeX] using hX
  have hmiddle :
      (R.eval (Polynomial.C L)).derivative.eval
        (Polynomial.C x) = 0 := by
    rw [derivative_eval_C_eq_triCoeffDerivativeX_eval]
    exact hmiddleRaw
  have houter :
      (R.derivative.eval (Polynomial.C L)).eval
        (Polynomial.C x) = 0 := by
    rw [eval_C_eval_commute]
    simpa only [L, triSpecializeX, Polynomial.derivative_map] using hY
  exact C_X_sq_dvd_ramifiedSubstitute_of_singular
    R (Polynomial.C x) L hzero hmiddle houter

end ProximityPrize.SubmissionLower
