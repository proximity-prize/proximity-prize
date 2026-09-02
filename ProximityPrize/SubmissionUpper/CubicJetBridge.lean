/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A tripled-zero quotient bridge for a 137-fibre attack

The proposed lower `67.67` architecture continues repeated-factor peeling to
a third contact derivative.  On the upper side, the corresponding direct
construction fixes the constant, linear, and quadratic coefficients of two
selector polynomials.  Their difference `P` is then divisible by `X^3`.
Subtracting

`(P.eval alpha / alpha^3) * X^3`

adds an off-grid root `alpha` without disturbing the triple root.  A
degree-131 difference leaves a quotient of degree at most 127 after division
by `X^3 * (X - C alpha)`.  At projected block size 1024 this permits 137
selected fibres and prospective agreement 141311.

This module proves the deterministic algebra and exact benchmark receipts.
It does not prove the required inclusive selector-fibre count.
-/

namespace ProximityPrize.SubmissionUpper.CubicJetBridge

open Polynomial

variable {F : Type*} [Field F]

noncomputable def cubicGamma (P : Polynomial F) (alpha : F) : F :=
  P.eval alpha / alpha ^ 3

noncomputable def cubicPencil (P : Polynomial F) (alpha : F) : Polynomial F :=
  P - Polynomial.C (cubicGamma P alpha) * Polynomial.X ^ 3

theorem cubicPencil_coeff_zero (P : Polynomial F) (alpha : F) :
    (cubicPencil P alpha).coeff 0 = P.coeff 0 := by
  simp [cubicPencil]

theorem cubicPencil_coeff_one (P : Polynomial F) (alpha : F) :
    (cubicPencil P alpha).coeff 1 = P.coeff 1 := by
  simp [cubicPencil]

theorem cubicPencil_coeff_two (P : Polynomial F) (alpha : F) :
    (cubicPencil P alpha).coeff 2 = P.coeff 2 := by
  simp [cubicPencil]

theorem cubicPencil_eval_alpha (P : Polynomial F) {alpha : F}
    (halpha : alpha ≠ 0) :
    (cubicPencil P alpha).eval alpha = 0 := by
  rw [cubicPencil, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, cubicGamma,
    div_mul_cancel₀ _ (pow_ne_zero 3 halpha), sub_self]

/-- Three matching low coefficients and the normalized off-grid evaluation
supply four linear factors. -/
theorem exists_cubic_quotient {P : Polynomial F} {alpha : F}
    (halpha : alpha ≠ 0)
    (hzero : P.coeff 0 = 0) (hone : P.coeff 1 = 0)
    (htwo : P.coeff 2 = 0) :
    ∃ Q : Polynomial F,
      cubicPencil P alpha =
        Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C alpha) * Q := by
  have hx3 : Polynomial.X ^ 3 ∣ cubicPencil P alpha := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simpa [cubicPencil_coeff_zero] using hzero
    · simpa [cubicPencil_coeff_one] using hone
    · simpa [cubicPencil_coeff_two] using htwo
  obtain ⟨Q1, hQ1⟩ := hx3
  have hqeval : Q1.eval alpha = 0 := by
    have hp := cubicPencil_eval_alpha P halpha
    rw [hQ1, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 3 halpha)
  have ha : Polynomial.X - Polynomial.C alpha ∣ Q1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hqeval
  obtain ⟨Q, hQ⟩ := ha
  refine ⟨Q, ?_⟩
  rw [hQ1, hQ, mul_assoc]

theorem cubicPencil_natDegree_le {P : Polynomial F} {alpha : F} {d : ℕ}
    (hP : P.natDegree ≤ d) (hd : 3 ≤ d) :
    (cubicPencil P alpha).natDegree ≤ d := by
  calc
    (cubicPencil P alpha).natDegree ≤
        max P.natDegree
          (Polynomial.C (cubicGamma P alpha) * Polynomial.X ^ 3).natDegree := by
      exact Polynomial.natDegree_sub_le _ _
    _ ≤ d := by
      apply max_le hP
      calc
        (Polynomial.C (cubicGamma P alpha) * Polynomial.X ^ 3).natDegree ≤
            (Polynomial.C (cubicGamma P alpha)).natDegree +
              (Polynomial.X ^ 3 : Polynomial F).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ d := by simp; omega

/-- Four forced factors turn a degree-`d` selector difference into a quotient
of degree at most `d-4`. -/
theorem exists_cubic_quotient_natDegree_le
    {P : Polynomial F} {alpha : F} {d : ℕ}
    (halpha : alpha ≠ 0)
    (hzero : P.coeff 0 = 0) (hone : P.coeff 1 = 0)
    (htwo : P.coeff 2 = 0)
    (hP : P.natDegree ≤ d) (hd : 4 ≤ d) :
    ∃ Q : Polynomial F,
      cubicPencil P alpha =
          Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C alpha) * Q ∧
        Q.natDegree ≤ d - 4 := by
  obtain ⟨Q, hQ⟩ := exists_cubic_quotient halpha hzero hone htwo
  refine ⟨Q, hQ, ?_⟩
  by_cases hQzero : Q = 0
  · simp [hQzero]
  · have hfactor : Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C alpha) ≠
        (0 : Polynomial F) :=
      mul_ne_zero (pow_ne_zero 3 Polynomial.X_ne_zero)
        (Polynomial.X_sub_C_ne_zero alpha)
    have hdegree :=
      cubicPencil_natDegree_le (alpha := alpha) hP (by omega : 3 ≤ d)
    rw [hQ, Polynomial.natDegree_mul hfactor hQzero] at hdegree
    simp only [Polynomial.natDegree_mul (pow_ne_zero 3 Polynomial.X_ne_zero)
      (Polynomial.X_sub_C_ne_zero alpha), Polynomial.natDegree_pow,
      Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C] at hdegree
    omega

/-- Evaluation form of the cubic-jet affine received-word identity.  The
second received direction remains the same simple-pole row as in the square
construction. -/
theorem cubic_quotient_agrees
    {P A Q : Polynomial F} {alpha gamma u : F}
    (hu : u ≠ 0) (hualpha : u ≠ alpha)
    (hvalue : P.eval u = A.eval u)
    (hfactor : P - Polynomial.C gamma * Polynomial.X ^ 3 =
      Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C alpha) * Q) :
    A.eval u / (u ^ 3 * (u - alpha)) + gamma * (-1 / (u - alpha)) =
      Q.eval u := by
  have h := congrArg (Polynomial.eval u) hfactor
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [hvalue] at h
  field_simp [hu, sub_ne_zero.mpr hualpha]
  linear_combination h

theorem benchmark_degree_receipt : 1023 + 127 * 1024 = 131071 := by
  norm_num

theorem benchmark_agreement_receipt : 137 * 1024 + 1023 = 141311 := by
  norm_num

theorem benchmark_unsafe_index_receipt : 262144 - 141311 = 120833 := by
  norm_num

set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 300000 in
/-- Exact integer comparison behind the conditional `114.12`-bit endpoint. -/
theorem benchmark_score_nat : (2 : ℕ) ^ 218988 ≤ 141311 ^ 12800 := by
  decide

end ProximityPrize.SubmissionUpper.CubicJetBridge

#print axioms ProximityPrize.SubmissionUpper.CubicJetBridge.exists_cubic_quotient_natDegree_le
#print axioms ProximityPrize.SubmissionUpper.CubicJetBridge.cubic_quotient_agrees
