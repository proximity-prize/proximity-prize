/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A doubled-zero quotient bridge for the 1024-fibre attack

If two selector polynomials have the same constant and linear coefficients,
their difference `P` is divisible by `X ^ 2`.  Subtracting

`(P.eval alpha / alpha ^ 2) * X ^ 2`

adds the off-grid root `alpha` without disturbing that double root.  A degree
`130` difference therefore leaves a quotient of degree at most `127` after
division by `X ^ 2 * (X - C alpha)`.

This is the upper-side algebraic consequence suggested by the lower track's
square-divisibility selector.  It isolates the deterministic implication; a
large fibre with the required matching coefficients is a separate counting
obligation.
-/

namespace ProximityPrize.SubmissionUpper.SquareJetBridge

open Polynomial

variable {F : Type*} [Field F]

/-- Challenge extracted from an off-grid evaluation after normalizing by the
doubled zero at the origin. -/
noncomputable def squareGamma (P : Polynomial F) (alpha : F) : F :=
  P.eval alpha / alpha ^ 2

/-- The selector difference after subtracting its affine challenge column. -/
noncomputable def squarePencil (P : Polynomial F) (alpha : F) : Polynomial F :=
  P - Polynomial.C (squareGamma P alpha) * Polynomial.X ^ 2

theorem squarePencil_eval_zero (P : Polynomial F) (alpha : F) :
    (squarePencil P alpha).eval 0 = P.coeff 0 := by
  simp [squarePencil, Polynomial.coeff_zero_eq_eval_zero]

theorem squarePencil_coeff_one (P : Polynomial F) (alpha : F) :
    (squarePencil P alpha).coeff 1 = P.coeff 1 := by
  simp [squarePencil]

theorem squarePencil_eval_alpha (P : Polynomial F) {alpha : F}
    (halpha : alpha ≠ 0) :
    (squarePencil P alpha).eval alpha = 0 := by
  rw [squarePencil, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, squareGamma,
    div_mul_cancel₀ _ (pow_ne_zero 2 halpha), sub_self]

/-- Matching the constant and linear coefficients supplies a double zero;
the normalized off-grid evaluation supplies a third zero. -/
theorem exists_square_quotient {P : Polynomial F} {alpha : F}
    (halpha : alpha ≠ 0) (hzero : P.coeff 0 = 0) (hone : P.coeff 1 = 0) :
    ∃ Q : Polynomial F,
      squarePencil P alpha =
        Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C alpha) * Q := by
  have hx2 : Polynomial.X ^ 2 ∣ squarePencil P alpha := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [squarePencil_eval_zero, hzero, Polynomial.coeff_zero_eq_eval_zero]
    · simp [squarePencil_coeff_one, hone]
  obtain ⟨Q1, hQ1⟩ := hx2
  have hqeval : Q1.eval alpha = 0 := by
    have hp := squarePencil_eval_alpha P halpha
    rw [hQ1, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 halpha)
  have ha : Polynomial.X - Polynomial.C alpha ∣ Q1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hqeval
  obtain ⟨Q, hQ⟩ := ha
  refine ⟨Q, ?_⟩
  rw [hQ1, hQ, mul_assoc]

theorem squarePencil_natDegree_le {P : Polynomial F} {alpha : F} {d : ℕ}
    (hP : P.natDegree ≤ d) (hd : 2 ≤ d) :
    (squarePencil P alpha).natDegree ≤ d := by
  calc
    (squarePencil P alpha).natDegree ≤
        max P.natDegree
          (Polynomial.C (squareGamma P alpha) * Polynomial.X ^ 2).natDegree := by
      exact Polynomial.natDegree_sub_le _ _
    _ ≤ d := by
      apply max_le hP
      calc
        (Polynomial.C (squareGamma P alpha) * Polynomial.X ^ 2).natDegree ≤
            (Polynomial.C (squareGamma P alpha)).natDegree +
              (Polynomial.X ^ 2 : Polynomial F).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ d := by simp; omega

/-- The exact benchmark degree gain: three forced factors turn a degree-`d`
selector difference into a quotient of degree at most `d - 3`. -/
theorem exists_square_quotient_natDegree_le
    {P : Polynomial F} {alpha : F} {d : ℕ}
    (halpha : alpha ≠ 0) (hzero : P.coeff 0 = 0) (hone : P.coeff 1 = 0)
    (hP : P.natDegree ≤ d) (hd : 3 ≤ d) :
    ∃ Q : Polynomial F,
      squarePencil P alpha =
          Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C alpha) * Q ∧
        Q.natDegree ≤ d - 3 := by
  obtain ⟨Q, hQ⟩ := exists_square_quotient halpha hzero hone
  refine ⟨Q, hQ, ?_⟩
  by_cases hQzero : Q = 0
  · simp [hQzero]
  · have hfactor : Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C alpha) ≠
        (0 : Polynomial F) :=
      mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero)
        (Polynomial.X_sub_C_ne_zero alpha)
    have hdegree :=
      squarePencil_natDegree_le (alpha := alpha) hP (by omega : 2 ≤ d)
    rw [hQ, Polynomial.natDegree_mul hfactor hQzero] at hdegree
    simp only [Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero)
      (Polynomial.X_sub_C_ne_zero alpha), Polynomial.natDegree_pow,
      Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C] at hdegree
    omega

/-- Evaluation form of the resulting affine received-word identity. -/
theorem square_quotient_agrees
    {P A Q : Polynomial F} {alpha gamma u : F}
    (hu : u ≠ 0) (hualpha : u ≠ alpha)
    (hvalue : P.eval u = A.eval u)
    (hfactor : P - Polynomial.C gamma * Polynomial.X ^ 2 =
      Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C alpha) * Q) :
    A.eval u / (u ^ 2 * (u - alpha)) + gamma * (-1 / (u - alpha)) =
      Q.eval u := by
  have h := congrArg (Polynomial.eval u) hfactor
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [hvalue] at h
  field_simp [hu, sub_ne_zero.mpr hualpha]
  linear_combination h

/-! The two exact integer receipts for the proposed 1024-fibre instantiation. -/

theorem benchmark_degree_receipt : 1023 + 127 * 1024 = 131071 := by
  norm_num

theorem benchmark_agreement_receipt : 136 * 1024 + 1023 = 140287 := by
  norm_num

theorem benchmark_unsafe_index_receipt : 262144 - 140287 = 121857 := by
  norm_num

set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 300000 in
/-- The exact integer comparison behind the prospective `115.46`-bit score.
It is deliberately only an arithmetic receipt: the large selector fibre
needed to instantiate the construction remains a separate obligation. -/
theorem benchmark_score_nat : (2 : ℕ) ^ 218854 ≤ 140287 ^ 12800 := by
  decide

end ProximityPrize.SubmissionUpper.SquareJetBridge

#print axioms ProximityPrize.SubmissionUpper.SquareJetBridge.exists_square_quotient_natDegree_le
#print axioms ProximityPrize.SubmissionUpper.SquareJetBridge.square_quotient_agrees
