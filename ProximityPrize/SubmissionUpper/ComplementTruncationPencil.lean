/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Complement truncation and a monomial pencil

Let `L * R = X^N - 1`, and split the complementary factor as

`R = X^s * H + r * X^(s - 1) + E`.

If `gamma * r = -1`, multiplying the resulting quotient candidate by `X^s`
gives an expression involving only the locator `L` and the short residual
tail `E`.  At every root of `L`, the negative quotient evaluates as the
two-monomial pencil

`x^(A - 1) + gamma * x^(N - s)`.

This is the exact algebraic bridge behind the complement-truncation syndrome
experiment.  It deliberately does not assert that the residual high band can
be cancelled: at the current benchmark agreement it still has `8709`
coefficients.
-/

namespace ProximityPrize.SubmissionUpper.ComplementTruncationPencil

open Polynomial

variable {F : Type} [Field F]

/-- The quotient whose negative is the desired two-monomial word on roots of
the locator. -/
noncomputable def truncationQuotient (N A s : ℕ) (gamma : F)
    (L H : Polynomial F) : Polynomial F :=
  Polynomial.C gamma * L * H - Polynomial.C gamma * Polynomial.X ^ (N - s) -
    Polynomial.X ^ (A - 1)

/-- The target two-monomial pencil. -/
noncomputable def monomialPencil (N A s : ℕ) (gamma : F) : Polynomial F :=
  Polynomial.X ^ (A - 1) + Polynomial.C gamma * Polynomial.X ^ (N - s)

/-- The complement-truncation identity.  The hypotheses `s ≤ N` and
`1 ≤ A` are exactly what is needed to recombine the truncated exponents. -/
theorem X_pow_mul_truncationQuotient
    {N A s : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1) :
    Polynomial.X ^ s * truncationQuotient N A s gamma L H =
      Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
        Polynomial.C gamma * L * E - Polynomial.C gamma := by
  have hXN : (Polynomial.X : Polynomial F) ^ s * Polynomial.X ^ (N - s) =
      Polynomial.X ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hXA : (Polynomial.X : Polynomial F) ^ s * Polynomial.X ^ (A - 1) =
      Polynomial.X ^ (A + s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hH : (Polynomial.X : Polynomial F) ^ s * H =
      R - Polynomial.C r * Polynomial.X ^ (s - 1) - E := by
    linear_combination -htrunc
  dsimp only [truncationQuotient]
  calc
    Polynomial.X ^ s *
        (Polynomial.C gamma * L * H -
          Polynomial.C gamma * Polynomial.X ^ (N - s) -
            Polynomial.X ^ (A - 1)) =
        Polynomial.C gamma * L * (Polynomial.X ^ s * H) -
          Polynomial.C gamma * (Polynomial.X ^ s * Polynomial.X ^ (N - s)) -
            Polynomial.X ^ s * Polynomial.X ^ (A - 1) := by ring
    _ =
        Polynomial.C gamma * L * (Polynomial.X ^ s * H) -
          Polynomial.C gamma * Polynomial.X ^ N -
            Polynomial.X ^ (A + s - 1) := by
      rw [hXN, hXA]
    _ = Polynomial.C gamma * L *
          (R - Polynomial.C r * Polynomial.X ^ (s - 1) - E) -
          Polynomial.C gamma * Polynomial.X ^ N -
            Polynomial.X ^ (A + s - 1) := by rw [hH]
    _ = Polynomial.C gamma * (L * R) -
          (Polynomial.C gamma * Polynomial.C r) *
            (Polynomial.X ^ (s - 1) * L) - Polynomial.C gamma * L * E -
              Polynomial.C gamma * Polynomial.X ^ N -
                Polynomial.X ^ (A + s - 1) := by ring
    _ = Polynomial.C gamma * (Polynomial.X ^ N - 1) -
          (Polynomial.C gamma * Polynomial.C r) *
            (Polynomial.X ^ (s - 1) * L) - Polynomial.C gamma * L * E -
              Polynomial.C gamma * Polynomial.X ^ N -
                Polynomial.X ^ (A + s - 1) := by rw [hgrid]
    _ = Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
          Polynomial.C gamma * L * E - Polynomial.C gamma := by
      simp only [← Polynomial.C_mul, hgamma, Polynomial.C_neg,
        Polynomial.C_1]
      ring

/-- Multiplication by `X^s` transfers a degree bound on the residual side of
the identity back to the quotient. -/
theorem truncationQuotient_natDegree_le
    {N A s D : ℕ} {gamma r : F} {L R H E : Polynomial F}
    (hsN : s ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : R = Polynomial.X ^ s * H +
      Polynomial.C r * Polynomial.X ^ (s - 1) + E)
    (hgamma : gamma * r = -1)
    (hresidual : (Polynomial.X ^ (s - 1) * L -
      Polynomial.X ^ (A + s - 1) - Polynomial.C gamma * L * E -
        Polynomial.C gamma).natDegree ≤ D + s) :
    (truncationQuotient N A s gamma L H).natDegree ≤ D := by
  by_cases hQ : truncationQuotient N A s gamma L H = 0
  · simp [hQ]
  · have hX : (Polynomial.X : Polynomial F) ^ s ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have hbound : (Polynomial.X ^ s *
        truncationQuotient N A s gamma L H).natDegree ≤ D + s := by
      rw [X_pow_mul_truncationQuotient hsN hA hgrid htrunc hgamma]
      exact hresidual
    rw [Polynomial.natDegree_mul hX hQ, Polynomial.natDegree_X_pow] at hbound
    omega

/-- If the locator is monic of degree `A` and `E` is the residual tail below
`X^(s - 1)`, then the leading terms in the residual identity cancel. -/
theorem truncationResidual_natDegree_le
    {A s : ℕ} {gamma : F} {L E : Polynomial F}
    (hs : 2 ≤ s) (hA : 1 ≤ A) (hLmonic : L.Monic)
    (hLdegree : L.natDegree = A) (hE : E.natDegree ≤ s - 2) :
    (Polynomial.X ^ (s - 1) * L - Polynomial.X ^ (A + s - 1) -
      Polynomial.C gamma * L * E - Polynomial.C gamma).natDegree ≤
        A + s - 2 := by
  have hlead : (Polynomial.X ^ (s - 1) * L -
      Polynomial.X ^ (A + s - 1)).natDegree ≤ A + s - 2 := by
    have hproductDegree : (Polynomial.X ^ (s - 1) * L).natDegree = A + s - 1 := by
      rw [Polynomial.natDegree_X_pow_mul (s - 1) hLmonic.ne_zero, hLdegree]
      omega
    have htop : (Polynomial.X ^ (s - 1) * L).coeff (A + s - 1) = 1 := by
      calc
        (Polynomial.X ^ (s - 1) * L).coeff (A + s - 1) = L.coeff A := by
          rw [show A + s - 1 = A + (s - 1) by omega]
          exact Polynomial.coeff_X_pow_mul L (s - 1) A
        _ = 1 := by rw [← hLdegree]; exact hLmonic.coeff_natDegree
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hnj : A + s - 1 ≤ j := by omega
    by_cases hjn : j = A + s - 1
    · subst j
      rw [Polynomial.coeff_sub, htop, Polynomial.coeff_X_pow_self, sub_self]
    · have hnltj : A + s - 1 < j :=
        lt_of_le_of_ne hnj (fun h ↦ hjn h.symm)
      rw [Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt (hproductDegree.symm ▸ hnltj),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          ((Polynomial.natDegree_X_pow (R := F) (A + s - 1)).symm ▸ hnltj),
        sub_zero]
  have htail : (Polynomial.C gamma * L * E).natDegree ≤ A + s - 2 := by
    calc
      (Polynomial.C gamma * L * E).natDegree ≤
          (Polynomial.C gamma * L).natDegree + E.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (Polynomial.C gamma).natDegree + L.natDegree + E.natDegree := by
        exact Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ A + s - 2 := by
        rw [Polynomial.natDegree_C, hLdegree]
        omega
  have hconstant : (Polynomial.C gamma : Polynomial F).natDegree ≤ A + s - 2 := by
    rw [Polynomial.natDegree_C]
    omega
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le
      ((Polynomial.natDegree_sub_le _ _).trans (max_le hlead htail))
      hconstant)

/-- At a root of the locator, the negative truncation quotient evaluates to
the corresponding two-monomial pencil value. -/
theorem eval_neg_truncationQuotient_at_root
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      x ^ (A - 1) + gamma * x ^ (N - s) := by
  simp only [truncationQuotient, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, hx, mul_zero, zero_mul, neg_sub]
  ring

/-- Equivalently, the two polynomials agree at every root of `L`. -/
theorem eval_neg_truncationQuotient_eq_monomialPencil_at_root
    {N A s : ℕ} {gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (-truncationQuotient N A s gamma L H).eval x =
      (monomialPencil N A s gamma).eval x := by
  rw [eval_neg_truncationQuotient_at_root hx]
  simp [monomialPencil]

/-! ## Exact benchmark receipts -/

/-- The current candidate agreement exceeds the row-code dimension by
exactly `8711`. -/
theorem benchmark_agreement_degree_gap : 139782 - 131071 = 8711 := by
  norm_num

/-- After the leading cancellation, the shifted quotient-degree gate leaves
`8709` residual high-band coefficients in the complement-truncation
construction. -/
theorem benchmark_residual_high_band_count :
    139782 - 131071 - 2 = 8709 := by
  norm_num

/-- Counting the inclusive residual band directly gives the same number,
independently of the truncation depth `s`. -/
theorem benchmark_residual_high_band_width (s : ℕ) :
    (139782 + s - 2) - (131071 + s + 1) + 1 = 8709 := by
  omega

#print axioms X_pow_mul_truncationQuotient
#print axioms truncationQuotient_natDegree_le
#print axioms truncationResidual_natDegree_le
#print axioms eval_neg_truncationQuotient_at_root

end ProximityPrize.SubmissionUpper.ComplementTruncationPencil
