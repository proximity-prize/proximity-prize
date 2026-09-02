/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Grid-equivalent Padé presentations

Two rational presentations which agree on the full compressed evaluation grid
do not automatically provide two independent branches of an upper-bound
construction.  When the locator divides the grid polynomial, a Padé solution
for one presentation transports to the other with the *same* quotient.

This is the exact algebra behind the apparent ``two-parent'' freedom in the
`256`-label upper cell.  The coprimality hypothesis is the usual requirement
that the first denominator have no selected-label root.
-/

namespace ProximityPrize.SubmissionUpper.GridEquivalentPadeBridge

open Polynomial

variable {F : Type} [Field F]

/-- Transport a Padé solution between two rational pencils whose numerator
cross-differences are multiples of a grid polynomial `G = V * W`.

The transported solution uses the same `Q`; only the auxiliary cofactor
changes.  Thus, under matching degree bounds on the cofactors, changing to a
grid-equivalent denominator is a gauge transformation rather than a source
of additional challenge branches. -/
theorem exists_same_quotient_of_grid_equivalent
    {G V W D₁ D₂ A₁ A₂ B₁ B₂ S_A S_B Q H₁ : Polynomial F} {gamma : F}
    (hgrid : G = V * W)
    (hA : A₁ * D₂ = A₂ * D₁ + G * S_A)
    (hB : B₁ * D₂ = B₂ * D₁ + G * S_B)
    (hcop : IsCoprime D₁ V)
    (hD₁ : D₁ ≠ 0)
    (hsol : D₁ * Q = H₁ * V - A₁ - Polynomial.C gamma * B₁) :
    ∃ H₂ : Polynomial F,
      D₂ * Q = H₂ * V - A₂ - Polynomial.C gamma * B₂ ∧
      D₂ * H₁ - W * (S_A + Polynomial.C gamma * S_B) = D₁ * H₂ := by
  let S : Polynomial F := S_A + Polynomial.C gamma * S_B
  have hmultiple :
      D₁ * (D₂ * Q + A₂ + Polynomial.C gamma * B₂) =
        V * (D₂ * H₁ - W * S) := by
    dsimp only [S]
    linear_combination D₂ * hsol - hA - Polynomial.C gamma * hB -
      (S_A + Polynomial.C gamma * S_B) * hgrid
  have hdvdmul : D₁ ∣ V * (D₂ * H₁ - W * S) := by
    rw [← hmultiple]
    exact dvd_mul_right D₁ _
  have hdvd : D₁ ∣ D₂ * H₁ - W * S :=
    hcop.dvd_of_dvd_mul_left hdvdmul
  obtain ⟨H₂, hH₂⟩ := hdvd
  refine ⟨H₂, ?_, by simpa only [S] using hH₂⟩
  · apply mul_left_cancel₀ hD₁
    linear_combination hmultiple + V * hH₂

/-- If the cross-difference transport numerator has the expected degree, the
new cofactor satisfies the same cap as the old one.  This is the precise
condition needed to turn the preceding algebraic transport into a no-new-
branch statement for a bounded Padé construction. -/
theorem exists_same_quotient_of_grid_equivalent_degree_le
    {G V W D₁ D₂ A₁ A₂ B₁ B₂ S_A S_B Q H₁ : Polynomial F}
    {gamma : F} {e : ℕ}
    (hgrid : G = V * W)
    (hA : A₁ * D₂ = A₂ * D₁ + G * S_A)
    (hB : B₁ * D₂ = B₂ * D₁ + G * S_B)
    (hcop : IsCoprime D₁ V)
    (hD₁ : D₁ ≠ 0)
    (hsol : D₁ * Q = H₁ * V - A₁ - Polynomial.C gamma * B₁)
    (htransportDegree :
      (D₂ * H₁ - W * (S_A + Polynomial.C gamma * S_B)).natDegree ≤
        D₁.natDegree + e) :
    ∃ H₂ : Polynomial F,
      D₂ * Q = H₂ * V - A₂ - Polynomial.C gamma * B₂ ∧
      H₂.natDegree ≤ e := by
  obtain ⟨H₂, hsolution, htransport⟩ :=
    exists_same_quotient_of_grid_equivalent hgrid hA hB hcop hD₁ hsol
  refine ⟨H₂, hsolution, ?_⟩
  by_cases hH₂ : H₂ = 0
  · simp [hH₂]
  · rw [htransport, Polynomial.natDegree_mul hD₁ hH₂] at htransportDegree
    omega

end ProximityPrize.SubmissionUpper.GridEquivalentPadeBridge

#print axioms ProximityPrize.SubmissionUpper.GridEquivalentPadeBridge.exists_same_quotient_of_grid_equivalent
#print axioms ProximityPrize.SubmissionUpper.GridEquivalentPadeBridge.exists_same_quotient_of_grid_equivalent_degree_le
