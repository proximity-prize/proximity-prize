/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Complementary-factor inverse for a locator derivative

When a squarefree locator `L` divides `X^N - 1`, its complementary factor
supplies a low-degree inverse of `L'` modulo `L`.  This is the exact algebraic
bridge needed to audit self-derivative proposals for the upper benchmark.
-/

namespace ProximityPrize.SubmissionUpper.ComplementDerivativeBridge

open Polynomial

variable {F : Type} [Field F]

/-- The low-degree Bézout coefficient supplied by a complementary factor. -/
noncomputable def complementDerivativeInverse (m : ℕ) (R : Polynomial F) : Polynomial F :=
  Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * R

/-- If `L * R = X^(m+1)-1`, the complementary factor gives an explicit inverse
of `L'` modulo `L`. -/
theorem complementDerivativeInverse_mul_derivative_sub_one
    (m : ℕ) (L R : Polynomial F) (hm : (((m + 1 : ℕ) : F)) ≠ 0)
    (hfactor : L * R = Polynomial.X ^ (m + 1) - 1) :
    complementDerivativeInverse m R * L.derivative - 1 =
      L * (R - Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * R.derivative) := by
  have hderivative := congrArg Polynomial.derivative hfactor
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X_pow_succ, Polynomial.derivative_one, sub_zero] at hderivative
  have hcast : (m : F) + 1 = ((m + 1 : ℕ) : F) := by norm_num
  rw [hcast] at hderivative
  have hmain :
      Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X *
        (Polynomial.C (((m + 1 : ℕ) : F)) * Polynomial.X ^ m) =
          Polynomial.X ^ (m + 1) := by
    calc
      Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X *
          (Polynomial.C (((m + 1 : ℕ) : F)) * Polynomial.X ^ m) =
          Polynomial.C ((((m + 1 : ℕ) : F)⁻¹) * ((m + 1 : ℕ) : F)) *
            (Polynomial.X * Polynomial.X ^ m) := by
              rw [Polynomial.C_mul]
              ring
      _ = Polynomial.X ^ (m + 1) := by
        rw [inv_mul_cancel₀ hm, Polynomial.C_1, one_mul, pow_succ']
  dsimp [complementDerivativeInverse]
  calc
    Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * R * L.derivative - 1 =
        Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X *
          (L.derivative * R + L * R.derivative) -
          Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * L * R.derivative - 1 := by ring
    _ = Polynomial.X ^ (m + 1) -
          Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * L * R.derivative - 1 := by
      rw [hderivative]
      rw [hmain]
    _ = (Polynomial.X ^ (m + 1) - 1) -
          Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * L * R.derivative := by ring
    _ = L * R -
          Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X * L * R.derivative := by
      rw [← hfactor]
    _ = L * (R - Polynomial.C (((m + 1 : ℕ) : F)⁻¹) *
          Polynomial.X * R.derivative) := by ring

theorem complementDerivativeInverse_isInverse
    (m : ℕ) (L R : Polynomial F)
    (hm : (((m + 1 : ℕ) : F)) ≠ 0)
    (hfactor : L * R = Polynomial.X ^ (m + 1) - 1) :
    L ∣ complementDerivativeInverse m R * L.derivative - 1 := by
  have hbezout := complementDerivativeInverse_mul_derivative_sub_one m L R hm hfactor
  refine ⟨R - Polynomial.C (((m + 1 : ℕ) : F)⁻¹) *
    Polynomial.X * R.derivative, ?_⟩
  exact hbezout

theorem eval_complementDerivativeInverse_mul_derivative
    (m : ℕ) (L R : Polynomial F) (hm : (((m + 1 : ℕ) : F)) ≠ 0)
    (hfactor : L * R = Polynomial.X ^ (m + 1) - 1)
    {x : F} (hx : L.eval x = 0) :
    (complementDerivativeInverse m R).eval x * L.derivative.eval x = 1 := by
  have hbezout := congrArg (Polynomial.eval x)
    (complementDerivativeInverse_mul_derivative_sub_one m L R hm hfactor)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one, hx,
    zero_mul] at hbezout
  exact sub_eq_zero.mp hbezout

theorem complementDerivativeInverse_natDegree_le (m : ℕ) (R : Polynomial F) :
    (complementDerivativeInverse m R).natDegree ≤ R.natDegree + 1 := by
  calc
    (complementDerivativeInverse m R).natDegree ≤
        (Polynomial.C (((m + 1 : ℕ) : F)⁻¹) * Polynomial.X).natDegree + R.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + R.natDegree := by
      exact Nat.add_le_add_right (Polynomial.natDegree_mul_le.trans (by simp)) _
    _ = R.natDegree + 1 := by omega

/-- In the 136-by-1024 candidate geometry, the inverse supplied by the
122880-degree complementary locator is itself a legal row polynomial. -/
theorem benchmark_complementDerivativeInverse_natDegree_le
    (R : Polynomial F) (hR : R.natDegree ≤ 122880) :
    (complementDerivativeInverse 262143 R).natDegree ≤ 122881 := by
  exact (complementDerivativeInverse_natDegree_le 262143 R).trans (by omega)

end ProximityPrize.SubmissionUpper.ComplementDerivativeBridge
