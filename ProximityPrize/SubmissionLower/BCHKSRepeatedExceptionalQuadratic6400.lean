import ProximityPrize.SubmissionLower.BCHKSRepeatedBlowupContent6400

/-!
# The exceptional divisor of the repeated-branch blow-up is quadratic

The generic Hensel ledger sees the full outer degree of a relation.  The
ramified transform has a stronger Newton-polygon property which that ledger
forgets: after removing the common `X^2`, its coefficient of slope degree `n`
is divisible by `X^(n-2)`.  Consequently, restriction to the exceptional
divisor `X = 0` has slope degree at most two, regardless of the original
outer degree.

This is the structural input needed for a valuation-aware lift whose cost can
depend on the exceptional degree rather than the global degree.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- After removing the common quadratic content, the coefficient of slope
degree `n` retains `X^(n-2)` divisibility. -/
theorem X_pow_sub_two_dvd_ramifiedDeflation_coeff
    {A : Type} [CommRing A] [IsDomain A]
    (B Q : A[X][Y]) (x y : A) (n : ℕ) (hn : 2 ≤ n)
    (hdef : ramifiedSubstitute B x y =
      Polynomial.C (Polynomial.X ^ 2) * Q) :
    Polynomial.X ^ (n - 2) ∣ Q.coeff n := by
  have hcoeff := congrArg (fun T : A[X][Y] ↦ T.coeff n) hdef
  simp only [Polynomial.coeff_C_mul] at hcoeff
  have hdiv : Polynomial.X ^ n ∣
      Polynomial.X ^ 2 * Q.coeff n := by
    rw [← hcoeff]
    exact X_pow_dvd_ramifiedSubstitute_coeff B x y n
  have hpow : (Polynomial.X : A[X]) ^ n =
      Polynomial.X ^ 2 * Polynomial.X ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hdiv
  exact (mul_dvd_mul_iff_left (by simp :
    (Polynomial.X : A[X]) ^ 2 ≠ 0)).mp hdiv

/-- Restrict a deflated relation to the exceptional divisor `X = 0` in
the centered coefficient variable. -/
noncomputable def exceptionalSpecialization
    {A : Type} [CommRing A] (Q : A[X][Y]) : A[X] :=
  Q.map (Polynomial.evalRingHom 0)

/-- Every slope coefficient above degree two vanishes on the exceptional
divisor. -/
theorem exceptionalSpecialization_coeff_eq_zero_of_two_lt
    {A : Type} [CommRing A] [IsDomain A]
    (B Q : A[X][Y]) (x y : A)
    (hdef : ramifiedSubstitute B x y =
      Polynomial.C (Polynomial.X ^ 2) * Q)
    (n : ℕ) (hn : 2 < n) :
    (exceptionalSpecialization Q).coeff n = 0 := by
  rw [exceptionalSpecialization, Polynomial.coeff_map]
  obtain ⟨c, hc⟩ := X_pow_sub_two_dvd_ramifiedDeflation_coeff
    B Q x y n (by omega) hdef
  rw [hc]
  simp [show n - 2 ≠ 0 by omega]

/-- The exceptional equation has slope degree at most two, independently of
the full slope degree of the deflated relation. -/
theorem exceptionalSpecialization_natDegree_le_two
    {A : Type} [CommRing A] [IsDomain A]
    (B Q : A[X][Y]) (x y : A)
    (hdef : ramifiedSubstitute B x y =
      Polynomial.C (Polynomial.X ^ 2) * Q) :
    (exceptionalSpecialization Q).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact exceptionalSpecialization_coeff_eq_zero_of_two_lt
    B Q x y hdef n hn

variable {F : Type} [Field F]

/-- Removing the common `X^2` content preserves every exact transformed
section. -/
theorem ramifiedDeflation_exact_root
    (B Q : F[X][Y]) (P : F[X]) (x y : F)
    (hxy : P.eval x = y) (hExact : B.eval P = 0)
    (hdef : ramifiedSubstitute B x y =
      Polynomial.C (Polynomial.X ^ 2) * Q) :
    Q.eval (centeredSectionQuotient P x y) = 0 := by
  have hroot := ramifiedSubstitute_exact_root B P x y hxy hExact
  rw [hdef] at hroot
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (by simp)

/-- The value of the transformed section on the exceptional divisor is the
ordinary derivative (the tangent slope) of the original section. -/
theorem centeredSectionQuotient_eval_zero
    (P : F[X]) (x y : F) (hxy : P.eval x = y) :
    (centeredSectionQuotient P x y).eval 0 = P.derivative.eval x := by
  have h := congrArg (fun T : F[X] ↦ T.coeff 1)
    (X_mul_centeredSectionQuotient P x y hxy)
  have htaylor : P.comp (Polynomial.C x + Polynomial.X) =
      Polynomial.taylor x P := by
    simp only [Polynomial.taylor_apply]
    congr 1
    exact add_comm _ _
  rw [htaylor] at h
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

/-- Evaluating a slope section and then restricting to the exceptional
divisor commutes with first restricting the relation and the section. -/
theorem exceptionalSpecialization_eval
    (Q : F[X][Y]) (W : F[X]) :
    (exceptionalSpecialization Q).eval (W.eval 0) =
      (Q.eval W).eval 0 := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      change (Q.map (Polynomial.evalRingHom 0)).eval (W.eval 0) =
        (Q.eval W).eval 0 at hQ
      change (R.map (Polynomial.evalRingHom 0)).eval (W.eval 0) =
        (R.eval W).eval 0 at hR
      change ((Q + R).map (Polynomial.evalRingHom 0)).eval (W.eval 0) =
        ((Q + R).eval W).eval 0
      rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add,
        Polynomial.eval_add]
      exact congrArg₂ (fun a b : F ↦ a + b) hQ hR
  | monomial n c =>
      simp [exceptionalSpecialization, Polynomial.map_monomial,
        Polynomial.eval_monomial]

/-- Initial tangent slopes of exact sections lie on the same quadratic
exceptional equation. -/
theorem exceptionalSpecialization_eval_derivative_eq_zero
    (B Q : F[X][Y]) (P : F[X]) (x y : F)
    (hxy : P.eval x = y) (hExact : B.eval P = 0)
    (hdef : ramifiedSubstitute B x y =
      Polynomial.C (Polynomial.X ^ 2) * Q) :
    (exceptionalSpecialization Q).eval (P.derivative.eval x) = 0 := by
  have hroot := ramifiedDeflation_exact_root B Q P x y hxy hExact hdef
  have heval := congrArg (Polynomial.eval (0 : F)) hroot
  rw [← centeredSectionQuotient_eval_zero P x y hxy]
  rw [exceptionalSpecialization_eval]
  simpa using heval

end ProximityPrize.SubmissionLower
