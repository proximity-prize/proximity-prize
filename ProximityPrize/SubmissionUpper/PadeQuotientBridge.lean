/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Codeword invariance for the Padé high-coefficient obstruction

The fixed-denominator Padé audit uses a denominator of degree at most `e + 2`.
Adding a quotient polynomial of degree at most `127` changes the numerator by
`D * P`, whose degree is at most `e + 129`.  Consequently all coefficients from
degree `e + 130` onward are invariants of the residue class modulo `D`.

The final section records the same fact after the benchmark substitution
`Y = X^1024`.  It allows an arbitrary row-code polynomial of degree at most
`131071`, rather than only a polynomial in `Y`.
-/

namespace ProximityPrize.SubmissionUpper.PadeQuotientBridge

open Polynomial

variable {F : Type} [Field F]

/-- Multiplying a denominator of degree at most `e + 2` by a quotient of degree
at most `127` reaches degree at most `e + 129`. -/
theorem mul_natDegree_le_e_add_129 {e : ℕ} {D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 127) :
    (D * P).natDegree ≤ e + 129 := by
  exact Polynomial.natDegree_mul_le.trans (by omega)

/-- The product in the preceding lemma lies strictly below the first of the
seven high Padé coefficients. -/
theorem mul_natDegree_lt_e_add_130 {e : ℕ} {D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 127) :
    (D * P).natDegree < e + 130 := by
  exact (mul_natDegree_le_e_add_129 hD hP).trans_lt (by omega)

/-- Every coefficient of `D * P` in the Padé high band is zero. -/
theorem coeff_mul_eq_zero_of_e_add_130_le {e j : ℕ} {D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 127) (hj : e + 130 ≤ j) :
    (D * P).coeff j = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((mul_natDegree_lt_e_add_130 hD hP).trans_le hj)

/-! ## The complete Padé high band

The remainder condition by itself is not the whole bounded-quotient
condition.  At the benchmark value `e = 118`, a solution with
`deg D ≤ 120` and `deg Q ≤ 127` must also cancel all seven coefficients
in degrees `248,…,254`.  Together with the remainder-cofactor condition in
degree `119`, these are eight obligations.  The following lemmas record the
seven numerator equations without choosing coordinates for the convolution
`H * V`.
-/

/-- Every bounded Padé solution satisfies every high-band numerator
equation.  This is independent of how the cofactor `H` was obtained. -/
theorem high_band_equation_of_solution {e j : ℕ}
    {D Q H V A B : Polynomial F} {gamma : F}
    (hD : D.natDegree ≤ e + 2) (hQ : Q.natDegree ≤ 127)
    (hsol : D * Q = H * V - A - Polynomial.C gamma * B)
    (hj : e + 130 ≤ j) :
    (H * V).coeff j = A.coeff j + gamma * B.coeff j := by
  have hcoeff := congrArg (fun P : Polynomial F => P.coeff j) hsol
  rw [coeff_mul_eq_zero_of_e_add_130_le hD hQ hj] at hcoeff
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul] at hcoeff
  linear_combination -hcoeff

/-- For `e = 118`, the seven forbidden numerator coefficients are exactly
the consecutive degrees `248,…,254`. -/
theorem benchmark_high_band_equation_of_solution
    {D Q H V A B : Polynomial F} {gamma : F}
    (hD : D.natDegree ≤ 120) (hQ : Q.natDegree ≤ 127)
    (hsol : D * Q = H * V - A - Polynomial.C gamma * B)
    (i : Fin 7) :
    (H * V).coeff (248 + i.val) =
      A.coeff (248 + i.val) + gamma * B.coeff (248 + i.val) := by
  apply high_band_equation_of_solution (e := 118) hD hQ hsol
  omega

/-- The cofactor cap supplies the eighth benchmark obligation: its
degree-`119` coefficient vanishes. -/
theorem benchmark_cofactor_top_eq_zero {H : Polynomial F}
    (hH : H.natDegree ≤ 118) : H.coeff 119 = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hH.trans_lt (by norm_num))

/-- A compact statement of all eight necessary benchmark obligations.  It
is useful when auditing a proposed two-row minor: proving only two of these
conditions cannot establish the legal quotient bound. -/
theorem benchmark_eight_obligations_of_solution
    {D Q H V A B : Polynomial F} {gamma : F}
    (hD : D.natDegree ≤ 120) (hQ : Q.natDegree ≤ 127)
    (hH : H.natDegree ≤ 118)
    (hsol : D * Q = H * V - A - Polynomial.C gamma * B) :
    H.coeff 119 = 0 ∧
      ∀ i : Fin 7,
        (H * V).coeff (248 + i.val) =
          A.coeff (248 + i.val) + gamma * B.coeff (248 + i.val) := by
  exact ⟨benchmark_cofactor_top_eq_zero hH,
    fun i => benchmark_high_band_equation_of_solution hD hQ hsol i⟩

/-- If a polynomial has degree at most `254` and its seven coefficients in
degrees `248,…,254` vanish, then it has degree below `248`. -/
theorem natDegree_lt_248_of_high_band_zero {P : Polynomial F}
    (hP : P.natDegree ≤ 254)
    (hband : ∀ i : Fin 7, P.coeff (248 + i.val) = 0) :
    P.natDegree < 248 := by
  by_cases hPzero : P = 0
  · simp [hPzero]
  · rw [Polynomial.natDegree_lt_iff_degree_lt hPzero,
      Polynomial.degree_lt_iff_coeff_zero]
    intro d hd
    have hd248 : 248 ≤ d := by exact_mod_cast hd
    by_cases hd254 : d ≤ 254
    · let i : Fin 7 := ⟨d - 248, by omega⟩
      simpa only [i, Nat.add_sub_of_le hd248] using hband i
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega

/-- Conversely, for a degree-`120` nonzero denominator and a numerator of
degree at most `254`, the seven high-band cancellations force the quotient
degree to be at most `127`.  Thus the full high band is not just necessary;
under the benchmark ambient caps it is exactly the quotient-degree gate. -/
theorem benchmark_quotient_natDegree_le_of_high_band_zero
    {D Q N : Polynomial F}
    (hD : D ≠ 0) (hDdeg : D.natDegree = 120)
    (hN : N.natDegree ≤ 254) (hEq : D * Q = N)
    (hband : ∀ i : Fin 7, N.coeff (248 + i.val) = 0) :
    Q.natDegree ≤ 127 := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · have hlt := natDegree_lt_248_of_high_band_zero hN hband
    rw [← hEq, Polynomial.natDegree_mul hD hQ, hDdeg] at hlt
    omega

/-- Adding a degree-`127` quotient multiple cannot alter any coefficient at or
above degree `e + 130`. -/
theorem coeff_add_mul_eq_left_of_e_add_130_le {e j : ℕ} {A D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 127) (hj : e + 130 ≤ j) :
    (A + D * P).coeff j = A.coeff j := by
  rw [Polynomial.coeff_add, coeff_mul_eq_zero_of_e_add_130_le hD hP hj, add_zero]

/-- Equivalent representatives modulo `D` have the same high coefficients
when their difference is represented by an allowed quotient. -/
theorem coeff_eq_of_eq_add_mul_of_e_add_130_le {e j : ℕ}
    {A B D P : Polynomial F} (hB : B = A + D * P)
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 127) (hj : e + 130 ≤ j) :
    B.coeff j = A.coeff j := by
  rw [hB]
  exact coeff_add_mul_eq_left_of_e_add_130_le hD hP hj

/-- Independently of the degree bounds, adding a multiple of a monic
denominator does not change the polynomial remainder. -/
theorem add_mul_modByMonic (A D P : Polynomial F) (hD : D.Monic) :
    (A + D * P) %ₘ D = A %ₘ D := by
  rw [Polynomial.add_modByMonic, Polynomial.self_mul_modByMonic hD, add_zero]

/-! ## The full `X` variable after `Y = X^1024` -/

/-- A full row-code polynomial of degree at most `131071`, multiplied by
`D(X^1024)`, still lies strictly below the lifted high-coefficient cutoff.
This is the degree calculation
`1024 * (e + 2) + 131071 = 1024 * (e + 130) - 1`. -/
theorem comp_X_pow_1024_mul_natDegree_lt {e : ℕ} {D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 131071) :
    ((D.comp (Polynomial.X ^ 1024)) * P).natDegree < 1024 * (e + 130) := by
  have hcomp : (D.comp (Polynomial.X ^ 1024)).natDegree ≤ (e + 2) * 1024 := by
    calc
      (D.comp (Polynomial.X ^ 1024)).natDegree ≤
          D.natDegree * (Polynomial.X ^ 1024 : Polynomial F).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (e + 2) * 1024 := by
        rw [Polynomial.natDegree_X_pow]
        exact Nat.mul_le_mul_right 1024 hD
  have hmul := Polynomial.natDegree_mul_le
    (p := D.comp (Polynomial.X ^ 1024)) (q := P)
  omega

/-- The lifted product has zero coefficients throughout the forbidden band. -/
theorem coeff_comp_X_pow_1024_mul_eq_zero {e j : ℕ} {D P : Polynomial F}
    (hD : D.natDegree ≤ e + 2) (hP : P.natDegree ≤ 131071)
    (hj : 1024 * (e + 130) ≤ j) :
    ((D.comp (Polynomial.X ^ 1024)) * P).coeff j = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((comp_X_pow_1024_mul_natDegree_lt hD hP).trans_le hj)

/-- An arbitrary full row-code translation preserves every coefficient in the
lifted forbidden band. -/
theorem coeff_add_comp_X_pow_1024_mul_eq_left {e j : ℕ}
    {A D P : Polynomial F} (hD : D.natDegree ≤ e + 2)
    (hP : P.natDegree ≤ 131071) (hj : 1024 * (e + 130) ≤ j) :
    (A + (D.comp (Polynomial.X ^ 1024)) * P).coeff j = A.coeff j := by
  rw [Polynomial.coeff_add, coeff_comp_X_pow_1024_mul_eq_zero hD hP hj, add_zero]

/-- In the range used by the composed-locator audit, the entire shift remains
below the size `262144` of the benchmark evaluation domain. -/
theorem benchmark_comp_X_pow_1024_mul_natDegree_lt_domain {e : ℕ}
    {D P : Polynomial F} (he : e ≤ 119) (hD : D.natDegree ≤ e + 2)
    (hP : P.natDegree ≤ 131071) :
    ((D.comp (Polynomial.X ^ 1024)) * P).natDegree < 262144 := by
  have h := comp_X_pow_1024_mul_natDegree_lt hD hP
  omega

/-- The benchmark substitution of a monic denominator is again monic. -/
theorem monic_comp_X_pow_1024 {D : Polynomial F} (hD : D.Monic) :
    (D.comp (Polynomial.X ^ 1024)).Monic := by
  exact hD.comp (Polynomial.monic_X_pow 1024) (by norm_num [Polynomial.natDegree_X_pow])

/-- The full-variable codeword translation also leaves the remainder modulo
the lifted denominator unchanged. -/
theorem add_comp_X_pow_1024_mul_modByMonic (A D P : Polynomial F) (hD : D.Monic) :
    (A + (D.comp (Polynomial.X ^ 1024)) * P) %ₘ (D.comp (Polynomial.X ^ 1024)) =
      A %ₘ (D.comp (Polynomial.X ^ 1024)) := by
  exact add_mul_modByMonic A (D.comp (Polynomial.X ^ 1024)) P (monic_comp_X_pow_1024 hD)

end ProximityPrize.SubmissionUpper.PadeQuotientBridge

#print axioms ProximityPrize.SubmissionUpper.PadeQuotientBridge.benchmark_eight_obligations_of_solution
#print axioms ProximityPrize.SubmissionUpper.PadeQuotientBridge.benchmark_quotient_natDegree_le_of_high_band_zero
