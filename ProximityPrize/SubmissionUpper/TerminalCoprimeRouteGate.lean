/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Terminal-coprime gate for repeated locator replacement

The terminal-coprimality primitive already occurs in the lower score-6767
merge-base certificate.  The accepted score-6768, score-6775, and score-6776
development made it substantially more important by extending the adaptive
replacement route from one or two quotient stages through depths three to
seven.  The route tracks three weighted degrees of a quotient.  After
repeatedly dividing by one irreducible factor `F`, it stops as soon as one
residual degree is strictly smaller than the corresponding degree of `F`.
Divisibility would make that degree monotone, so the terminal quotient is
coprime to `F`.

This upper-only module isolates that transferable mechanism without importing
the lower submission or its coefficient boxes.  It shows that a fixed common
factor cannot support one more quotient layer after any terminal coordinate
has crossed below the factor.  Thus the sixth- and seventh-contact bridges do
not extend indefinitely: a putative upper attack must enter a coprime
intersection branch, use a singular factor, or make the factor depend on the
challenge.

The rank functions below are deliberately abstract.  In the accepted proof
they are weighted total degrees; in an upper construction they can instead be
ordinary degree, a Newton-polytope support function, or any other quantity
known to be monotone under the relevant divisibility relation.
-/

namespace ProximityPrize.SubmissionUpper.TerminalCoprimeRouteGate

/-- Any divisibility-monotone rank rules out divisibility once the putative
quotient has smaller rank than the factor. -/
theorem not_dvd_of_rank_lt
    {R : Type*} [Monoid R] (rank : R → ℕ) {F Q : R}
    (hmono : F ∣ Q → rank F ≤ rank Q) (hlt : rank Q < rank F) :
    ¬ F ∣ Q := by
  intro hdiv
  exact (not_lt_of_ge (hmono hdiv)) hlt

/-- If `F` is irreducible, the same rank drop promotes nondivisibility to
coprimality. -/
theorem isRelPrime_of_rank_lt
    {R : Type*} [Monoid R] (rank : R → ℕ) {F Q : R}
    (hF : Irreducible F) (hmono : F ∣ Q → rank F ≤ rank Q)
    (hlt : rank Q < rank F) : IsRelPrime F Q := by
  exact hF.isRelPrime_iff_not_dvd.mpr (not_dvd_of_rank_lt rank hmono hlt)

/-- Abstract form of the accepted three-coordinate terminal test.  After
`depth` copies of `F` have been removed, the quotient ranks are bounded by
the corresponding residual source budgets.  If any residual budget is below
the rank of `F`, another copy of `F` is impossible. -/
theorem terminal_route_not_dvd
    {R : Type*} [Monoid R]
    (rank₀ rank₁ rank₂ : R → ℕ) {F Q : R}
    (source₀ source₁ source₂ depth : ℕ)
    (hmono₀ : F ∣ Q → rank₀ F ≤ rank₀ Q)
    (hmono₁ : F ∣ Q → rank₁ F ≤ rank₁ Q)
    (hmono₂ : F ∣ Q → rank₂ F ≤ rank₂ Q)
    (hbound₀ : rank₀ Q ≤ source₀ - depth * rank₀ F)
    (hbound₁ : rank₁ Q ≤ source₁ - depth * rank₁ F)
    (hbound₂ : rank₂ Q ≤ source₂ - depth * rank₂ F)
    (hterminal :
      source₀ - depth * rank₀ F < rank₀ F ∨
      source₁ - depth * rank₁ F < rank₁ F ∨
      source₂ - depth * rank₂ F < rank₂ F) :
    ¬ F ∣ Q := by
  intro hdiv
  rcases hterminal with hterminal₀ | hterminal₁ | hterminal₂
  · exact (not_lt_of_ge ((hmono₀ hdiv).trans hbound₀)) hterminal₀
  · exact (not_lt_of_ge ((hmono₁ hdiv).trans hbound₁)) hterminal₁
  · exact (not_lt_of_ge ((hmono₂ hdiv).trans hbound₂)) hterminal₂

/-- Irreducibility turns the terminal three-coordinate route into precisely
the coprime branch needed by a resultant or intersection bound. -/
theorem terminal_route_isRelPrime
    {R : Type*} [Monoid R]
    (rank₀ rank₁ rank₂ : R → ℕ) {F Q : R}
    (source₀ source₁ source₂ depth : ℕ)
    (hF : Irreducible F)
    (hmono₀ : F ∣ Q → rank₀ F ≤ rank₀ Q)
    (hmono₁ : F ∣ Q → rank₁ F ≤ rank₁ Q)
    (hmono₂ : F ∣ Q → rank₂ F ≤ rank₂ Q)
    (hbound₀ : rank₀ Q ≤ source₀ - depth * rank₀ F)
    (hbound₁ : rank₁ Q ≤ source₁ - depth * rank₁ F)
    (hbound₂ : rank₂ Q ≤ source₂ - depth * rank₂ F)
    (hterminal :
      source₀ - depth * rank₀ F < rank₀ F ∨
      source₁ - depth * rank₁ F < rank₁ F ∨
      source₂ - depth * rank₂ F < rank₂ F) :
    IsRelPrime F Q := by
  apply hF.isRelPrime_iff_not_dvd.mpr
  exact terminal_route_not_dvd rank₀ rank₁ rank₂
    source₀ source₁ source₂ depth hmono₀ hmono₁ hmono₂
      hbound₀ hbound₁ hbound₂ hterminal

/-- A next common-factor layer contradicts the terminal route directly. -/
theorem no_next_common_factor_layer
    {R : Type*} [Monoid R]
    (rank₀ rank₁ rank₂ : R → ℕ) {F Q : R}
    (source₀ source₁ source₂ depth : ℕ)
    (hmono₀ : F ∣ Q → rank₀ F ≤ rank₀ Q)
    (hmono₁ : F ∣ Q → rank₁ F ≤ rank₁ Q)
    (hmono₂ : F ∣ Q → rank₂ F ≤ rank₂ Q)
    (hbound₀ : rank₀ Q ≤ source₀ - depth * rank₀ F)
    (hbound₁ : rank₁ Q ≤ source₁ - depth * rank₁ F)
    (hbound₂ : rank₂ Q ≤ source₂ - depth * rank₂ F)
    (hterminal :
      source₀ - depth * rank₀ F < rank₀ F ∨
      source₁ - depth * rank₁ F < rank₁ F ∨
      source₂ - depth * rank₂ F < rank₂ F)
    (hnext : F ∣ Q) : False := by
  exact terminal_route_not_dvd rank₀ rank₁ rank₂
    source₀ source₁ source₂ depth hmono₀ hmono₁ hmono₂
      hbound₀ hbound₁ hbound₂ hterminal hnext

#print axioms not_dvd_of_rank_lt
#print axioms isRelPrime_of_rank_lt
#print axioms terminal_route_not_dvd
#print axioms terminal_route_isRelPrime
#print axioms no_next_common_factor_layer

end ProximityPrize.SubmissionUpper.TerminalCoprimeRouteGate
