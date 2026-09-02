/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# An extension-valued complement pencil

Let `L * R = X^N - 1`.  Instead of truncating `R` itself, truncate the
twisted complement

`(1 + theta * X) * R = X^t * H + rho * X^(t - 1) + E`.

The adjacent complement coefficients are thereby packed into the single
extension-valued pivot `rho`.  If `gamma * rho = -1`, the quotient below has
an exact shifted identity whose only non-locator terms are the residual tail
and the linear twist.  At roots of `L` it evaluates as the explicit
three-monomial pencil

`-x^(A-1) - gamma * (theta * x^(N+1-t) + x^(N-t))`.

Over a quadratic extension, the pivot can carry two base-field coordinates.
The algebra below is field-generic; the companion deterministic audit checks
the two-coordinate syndrome mechanism on a toy quadratic extension and keeps
the benchmark entropy accounting external to Lean.
-/

namespace ProximityPrize.SubmissionUpper.ExtensionComplementPencil

open Polynomial

variable {F : Type} [Field F]

/-- The linear factor used to pack two adjacent complement coefficients. -/
noncomputable def twist (theta : F) : Polynomial F :=
  1 + Polynomial.C theta * Polynomial.X

/-- The high part produced by multiplying `X^t` through the twisted
complement truncation. -/
noncomputable def extensionHighQuotient (N t : ℕ) (theta : F) : Polynomial F :=
  Polynomial.C theta * Polynomial.X ^ (N + 1 - t) +
    Polynomial.X ^ (N - t)

/-- Quotient candidate associated to the extension-valued pivot. -/
noncomputable def extensionTruncationQuotient
    (N A t : ℕ) (theta gamma : F) (L H : Polynomial F) : Polynomial F :=
  Polynomial.C gamma * L * H -
    Polynomial.C gamma * extensionHighQuotient N t theta -
      Polynomial.X ^ (A - 1)

/-- The explicit polynomial seen by the verifier at roots of `L`. -/
noncomputable def extensionMonomialPencil
    (N A t : ℕ) (theta gamma : F) : Polynomial F :=
  -Polynomial.X ^ (A - 1) -
    Polynomial.C gamma * extensionHighQuotient N t theta

/-- Multiplication by `X^t` restores the two adjacent high monomials. -/
theorem X_pow_mul_extensionHighQuotient
    {N t : ℕ} {theta : F} (htN : t ≤ N) :
    Polynomial.X ^ t * extensionHighQuotient N t theta =
      Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N := by
  have hN : (Polynomial.X : Polynomial F) ^ t * Polynomial.X ^ (N - t) =
      Polynomial.X ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have hN1 : (Polynomial.X : Polynomial F) ^ t *
      Polynomial.X ^ (N + 1 - t) = Polynomial.X ^ (N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  dsimp only [extensionHighQuotient]
  rw [mul_add]
  calc
    Polynomial.X ^ t * (Polynomial.C theta * Polynomial.X ^ (N + 1 - t)) +
        Polynomial.X ^ t * Polynomial.X ^ (N - t) =
      Polynomial.C theta *
          (Polynomial.X ^ t * Polynomial.X ^ (N + 1 - t)) +
        Polynomial.X ^ t * Polynomial.X ^ (N - t) := by ring
    _ = Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N := by
      rw [hN1, hN]

/-- Expanding the twist against the roots-of-unity grid leaves exactly its
linear low part after removing the two high monomials. -/
theorem twist_mul_grid (N : ℕ) (theta : F) :
    twist theta * (Polynomial.X ^ N - 1) =
      (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
        (Polynomial.C theta * Polynomial.X + 1) := by
  have hsucc : (Polynomial.X : Polynomial F) * Polynomial.X ^ N =
      Polynomial.X ^ (N + 1) := by
    rw [← pow_succ']
  dsimp only [twist]
  calc
    (1 + Polynomial.C theta * Polynomial.X) * (Polynomial.X ^ N - 1) =
        Polynomial.C theta * (Polynomial.X * Polynomial.X ^ N) +
          Polynomial.X ^ N - (Polynomial.C theta * Polynomial.X + 1) := by ring
    _ = (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
          (Polynomial.C theta * Polynomial.X + 1) := by rw [hsucc]

/-- The extension-complement cancellation identity.  This is the formal
bridge from a twisted complement truncation to a short residual expression.
-/
theorem X_pow_mul_extensionTruncationQuotient
    {N A t : ℕ} {theta gamma rho : F} {L R H E : Polynomial F}
    (htN : t ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : twist theta * R = Polynomial.X ^ t * H +
      Polynomial.C rho * Polynomial.X ^ (t - 1) + E)
    (hgamma : gamma * rho = -1) :
    Polynomial.X ^ t *
        extensionTruncationQuotient N A t theta gamma L H =
      Polynomial.X ^ (t - 1) * L - Polynomial.X ^ (A + t - 1) -
        Polynomial.C gamma * L * E -
          Polynomial.C gamma * (Polynomial.C theta * Polynomial.X + 1) := by
  have hhigh := X_pow_mul_extensionHighQuotient (F := F) (theta := theta) htN
  have hXA : (Polynomial.X : Polynomial F) ^ t * Polynomial.X ^ (A - 1) =
      Polynomial.X ^ (A + t - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hH : (Polynomial.X : Polynomial F) ^ t * H =
      twist theta * R - Polynomial.C rho * Polynomial.X ^ (t - 1) - E := by
    linear_combination -htrunc
  dsimp only [extensionTruncationQuotient]
  calc
    Polynomial.X ^ t *
        (Polynomial.C gamma * L * H -
          Polynomial.C gamma * extensionHighQuotient N t theta -
            Polynomial.X ^ (A - 1)) =
      Polynomial.C gamma * L * (Polynomial.X ^ t * H) -
        Polynomial.C gamma *
          (Polynomial.X ^ t * extensionHighQuotient N t theta) -
            Polynomial.X ^ t * Polynomial.X ^ (A - 1) := by ring
    _ = Polynomial.C gamma * L * (Polynomial.X ^ t * H) -
        Polynomial.C gamma *
          (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
            Polynomial.X ^ (A + t - 1) := by rw [hhigh, hXA]
    _ = Polynomial.C gamma * L *
          (twist theta * R - Polynomial.C rho * Polynomial.X ^ (t - 1) - E) -
        Polynomial.C gamma *
          (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
            Polynomial.X ^ (A + t - 1) := by rw [hH]
    _ = Polynomial.C gamma * (twist theta * (L * R)) -
        (Polynomial.C gamma * Polynomial.C rho) *
          (Polynomial.X ^ (t - 1) * L) - Polynomial.C gamma * L * E -
            Polynomial.C gamma *
              (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
              Polynomial.X ^ (A + t - 1) := by ring
    _ = Polynomial.C gamma * (twist theta * (Polynomial.X ^ N - 1)) -
        (Polynomial.C gamma * Polynomial.C rho) *
          (Polynomial.X ^ (t - 1) * L) - Polynomial.C gamma * L * E -
            Polynomial.C gamma *
              (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
              Polynomial.X ^ (A + t - 1) := by rw [hgrid]
    _ = Polynomial.C gamma *
          ((Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
            (Polynomial.C theta * Polynomial.X + 1)) -
        (Polynomial.C gamma * Polynomial.C rho) *
          (Polynomial.X ^ (t - 1) * L) - Polynomial.C gamma * L * E -
            Polynomial.C gamma *
              (Polynomial.C theta * Polynomial.X ^ (N + 1) + Polynomial.X ^ N) -
              Polynomial.X ^ (A + t - 1) := by rw [twist_mul_grid]
    _ = Polynomial.X ^ (t - 1) * L - Polynomial.X ^ (A + t - 1) -
        Polynomial.C gamma * L * E -
          Polynomial.C gamma * (Polynomial.C theta * Polynomial.X + 1) := by
      simp only [← Polynomial.C_mul, hgamma, Polynomial.C_neg,
        Polynomial.C_1]
      ring

/-- A degree bound on the shifted residual transfers back to the quotient. -/
theorem extensionTruncationQuotient_natDegree_le
    {N A t D : ℕ} {theta gamma rho : F} {L R H E : Polynomial F}
    (htN : t ≤ N) (hA : 1 ≤ A)
    (hgrid : L * R = Polynomial.X ^ N - 1)
    (htrunc : twist theta * R = Polynomial.X ^ t * H +
      Polynomial.C rho * Polynomial.X ^ (t - 1) + E)
    (hgamma : gamma * rho = -1)
    (hresidual : (Polynomial.X ^ (t - 1) * L -
      Polynomial.X ^ (A + t - 1) - Polynomial.C gamma * L * E -
        Polynomial.C gamma * (Polynomial.C theta * Polynomial.X + 1)).natDegree ≤
          D + t) :
    (extensionTruncationQuotient N A t theta gamma L H).natDegree ≤ D := by
  by_cases hQ : extensionTruncationQuotient N A t theta gamma L H = 0
  · simp [hQ]
  · have hX : (Polynomial.X : Polynomial F) ^ t ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    have hbound : (Polynomial.X ^ t *
        extensionTruncationQuotient N A t theta gamma L H).natDegree ≤ D + t := by
      rw [X_pow_mul_extensionTruncationQuotient htN hA hgrid htrunc hgamma]
      exact hresidual
    rw [Polynomial.natDegree_mul hX hQ, Polynomial.natDegree_X_pow] at hbound
    omega

/-- At every locator root, the quotient evaluates as the explicit extension
monomial pencil. -/
theorem eval_extensionTruncationQuotient_eq_extensionMonomialPencil_at_root
    {N A t : ℕ} {theta gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (extensionTruncationQuotient N A t theta gamma L H).eval x =
      (extensionMonomialPencil N A t theta gamma).eval x := by
  simp only [extensionTruncationQuotient, extensionMonomialPencil,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_C, hx, mul_zero, zero_mul]
  ring

/-- Expanded evaluation bridge, convenient for a verifier working with field
values rather than polynomials. -/
theorem eval_extensionTruncationQuotient_at_root
    {N A t : ℕ} {theta gamma x : F} {L H : Polynomial F}
    (hx : L.eval x = 0) :
    (extensionTruncationQuotient N A t theta gamma L H).eval x =
      -x ^ (A - 1) -
        gamma * (theta * x ^ (N + 1 - t) + x ^ (N - t)) := by
  rw [eval_extensionTruncationQuotient_eq_extensionMonomialPencil_at_root hx]
  simp only [extensionMonomialPencil, extensionHighQuotient,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088

/-- A quadratic-extension challenge has more than enough values for the
current verifier threshold. -/
theorem benchmark_extension_pair_capacity :
    challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [challengeThreshold, baseFieldCardinality]

/-- The extension pair exceeds the threshold by this exact integer margin. -/
theorem benchmark_extension_pair_capacity_margin :
    baseFieldCardinality ^ 2 - challengeThreshold = 4264929175516188401 := by
  norm_num [challengeThreshold, baseFieldCardinality]

/-- After the two leading cancellations, the benchmark residual high band has
exactly `8709` coefficients. -/
theorem benchmark_residual_high_band_count :
    139782 - 131071 - 2 = 8709 := by
  norm_num

/-- Arithmetic-only receipt for the hundredth-symbol comparison checked by
the companion exact audit: `8709.00 - 8432.08 = 276.92`.  The Lean theorem
does not assert the external binomial entropy bound.
-/
theorem benchmark_hundredth_symbol_gap :
    8709 * 100 - 843208 = 27692 := by
  norm_num

#print axioms X_pow_mul_extensionTruncationQuotient
#print axioms extensionTruncationQuotient_natDegree_le
#print axioms eval_extensionTruncationQuotient_at_root
#print axioms benchmark_extension_pair_capacity

end ProximityPrize.SubmissionUpper.ExtensionComplementPencil
