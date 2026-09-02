/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Exceptional joint odd/even moment-fibre gate

The variable half-block survivor in the two-level dyadic attack has `255` available antipodal
pair labels.  Its best ordinary profile uses `128` signed partial pairs and `72` full pairs, so
`2 * 72 + 128 = 272`.  The first fifteen high coefficients split into eight odd signed moments
and seven even support moments.  Ordinary pigeonhole is short by more than `31.545` bits, leaving
only an unusually heavy joint fibre.

This file closes two natural ways of producing that fibre.

First, cancel the common roots of two selectors and let `A,B` be the two disjoint sides of the
resulting trade.  Equality of the first fifteen power sums gives equality of the first fifteen
elementary symmetric functions by Newton's identities; all indices are units because the
benchmark characteristic is greater than fifteen.  If `|A| = |B| <= 15`, this fixes both monic
root polynomials.  At size sixteen their only coefficient not supplied by those moments is the
constant coefficient, and the product key fixes it.  Therefore every nontrivial trade has at
least seventeen roots on each side, or at least 34 endpoint positions.  Pairwise-disjoint trade
cubes on the 510-point punctured endpoint pool have at most fifteen toggles and only `2^15`
records.

The formal theorem below starts at the coefficient interface, which is exactly the output of
the Newton step: coefficients `1,...,15`, the degree-sixteen coefficient, and the constant
product coefficient.  It then proves equality of the root multisets, rather than merely an
arithmetic proxy.

Second, a complete multiplicative dyadic coset annihilates moments `1,...,15` only when its
order is at least sixteen.  There are at most `512 / 16 = 32` such cosets, so even the generous
unpunctured union family has at most `2^32` records.  Fixed weight, the full/partial profile,
puncturing, and product matching only reduce this cap.

Neither result closes overlapping, non-coset global fibres.  Published moment-subset estimates
for sets of `n`th powers also do not reach this instance: realizing the 256-element subgroup
requires `n = (p-1)/256 = 8,323,072`, and their small-`n` hypotheses already fail for one moment.
The companion exact audit records those substitutions and the complete 119-profile frontier.
This is a scoped research gate, not a score claim.
-/

namespace ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

open Polynomial

/-! ## Coefficient and root-multiset rigidity through side size sixteen -/

variable {F : Type*} [Field F]

/-- The monic root polynomial of a multiset.  Multiplicity is retained so the theorem does not
silently assume square-freeness. -/
noncomputable def locator (roots : Multiset F) : Polynomial F :=
  (roots.map fun a => (Polynomial.X : Polynomial F) - Polynomial.C a).prod

/-- Coefficients `1,...,15`, the degree-sixteen coefficient, and the constant coefficient
determine every polynomial of degree at most sixteen. -/
theorem polynomial_eq_of_fifteen_coefficient_window_and_product
    (P Q : Polynomial F)
    (hP : P.natDegree ≤ 16) (hQ : Q.natDegree ≤ 16)
    (htop : ∀ k, 1 ≤ k → k ≤ 15 → P.coeff k = Q.coeff k)
    (hsixteen : P.coeff 16 = Q.coeff 16)
    (hconstant : P.coeff 0 = Q.coeff 0) :
    P = Q := by
  apply Polynomial.ext
  intro k
  by_cases hk0 : k = 0
  · simpa [hk0] using hconstant
  by_cases hk15 : k ≤ 15
  · exact htop k (Nat.one_le_iff_ne_zero.mpr hk0) hk15
  by_cases hk16 : k = 16
  · simpa [hk16] using hsixteen
  have hklarge : 16 < k := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hklarge),
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hklarge)]

/-- Two equal-size root multisets of side size at most sixteen are equal once their first
fifteen locator coefficients and products agree.  Vieta's formula supplies the constant
coefficient from the product, and taking polynomial roots recovers the multisets exactly. -/
theorem locator_eq_of_fifteen_coefficients_and_product
    (A B : Multiset F)
    (hcard : A.card = B.card) (hsmall : A.card ≤ 16)
    (htop : ∀ k, 1 ≤ k → k ≤ 15 → (locator A).coeff k = (locator B).coeff k)
    (hprod : A.prod = B.prod) :
    locator A = locator B := by
  have hAdegree : (locator A).natDegree ≤ 16 := by
    rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    exact hsmall
  have hBdegree : (locator B).natDegree ≤ 16 := by
    rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← hcard]
    exact hsmall
  have hsixteen : (locator A).coeff 16 = (locator B).coeff 16 := by
    by_cases hA16 : A.card = 16
    · have hB16 : B.card = 16 := hcard ▸ hA16
      change
        ((A.map fun a => (Polynomial.X : Polynomial F) - Polynomial.C a).prod).coeff 16 =
          ((B.map fun a => (Polynomial.X : Polynomial F) - Polynomial.C a).prod).coeff 16
      rw [Multiset.prod_X_sub_C_coeff A (by omega),
        Multiset.prod_X_sub_C_coeff B (by omega)]
      simp [hA16, hB16, Multiset.esymm]
    · have hAlt : A.card < 16 := by omega
      have hBlt : B.card < 16 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (by simpa [locator] using hAlt : (locator A).natDegree < 16),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by simpa [locator, ← hcard] using hBlt : (locator B).natDegree < 16)]
  have hconstant : (locator A).coeff 0 = (locator B).coeff 0 := by
    change
      ((A.map fun a => (Polynomial.X : Polynomial F) - Polynomial.C a).prod).coeff 0 =
        ((B.map fun a => (Polynomial.X : Polynomial F) - Polynomial.C a).prod).coeff 0
    rw [Multiset.prod_X_sub_C_coeff A (Nat.zero_le _),
      Multiset.prod_X_sub_C_coeff B (Nat.zero_le _)]
    have hAtop : A.esymm A.card = A.prod := by
      simp [Multiset.esymm, Multiset.powersetCard_self]
    have hBtop : B.esymm B.card = B.prod := by
      simp [Multiset.esymm, Multiset.powersetCard_self]
    rw [Nat.sub_zero, Nat.sub_zero, hAtop, hBtop, hcard, hprod]
  exact polynomial_eq_of_fifteen_coefficient_window_and_product
    (locator A) (locator B) hAdegree hBdegree htop hsixteen hconstant

/-- Root-polynomial equality gives actual equality of the traded multisets, including
multiplicity. -/
theorem multiset_eq_of_fifteen_coefficients_and_product
    (A B : Multiset F)
    (hcard : A.card = B.card) (hsmall : A.card ≤ 16)
    (htop : ∀ k, 1 ≤ k → k ≤ 15 → (locator A).coeff k = (locator B).coeff k)
    (hprod : A.prod = B.prod) :
    A = B := by
  have hroots := congrArg Polynomial.roots
    (locator_eq_of_fifteen_coefficients_and_product A B hcard hsmall htop hprod)
  simpa [locator] using hroots

/-- Contrapositive form used by the trade audit: a nontrivial same-key trade has at least
seventeen elements on each side. -/
theorem nontrivial_trade_side_at_least_seventeen
    (A B : Multiset F)
    (hcard : A.card = B.card)
    (htop : ∀ k, 1 ≤ k → k ≤ 15 → (locator A).coeff k = (locator B).coeff k)
    (hprod : A.prod = B.prod) (hne : A ≠ B) :
    17 ≤ A.card := by
  by_contra hnot
  have hsmall : A.card ≤ 16 := by omega
  exact hne (multiset_eq_of_fifteen_coefficients_and_product
    A B hcard hsmall htop hprod)

/-! ## Exact benchmark and scoped-family receipts -/

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088
def productStateCount : ℕ := 512

def pairLabels : ℕ := 255
def endpointPool : ℕ := 510
def bestPartialPairs : ℕ := 128
def bestFullPairs : ℕ := 72

def bestCandidateCount : ℕ :=
  38032759349297690082104258708171077594613775836502390708075581838007072 * 10 ^ 80 +
    54149008291804238489140361078627379620970549791324157348683096936272256565248000

def minimumTradeSide : ℕ := 17
def minimumTradeSupport : ℕ := 34
def maximumDisjointToggles : ℕ := 15

def minimumMomentNullCosetOrder : ℕ := 16
def maximumMomentNullCosets : ℕ := 32
def completeCosetUnionCap : ℕ := 4294967296

def puncturedCosetWeight272Family : ℕ := 265182525
def puncturedCosetProductFibreFloor : ℕ := 517935

def subgroupPowerExponent : ℕ := 8323072

theorem best_profile_ledger :
    2 * bestFullPairs + bestPartialPairs = 272 ∧
      bestFullPairs + bestPartialPairs ≤ pairLabels := by
  norm_num [bestFullPairs, bestPartialPairs, pairLabels]

/-- Exact failure of ordinary pigeonhole for the best separated profile. -/
theorem best_profile_ordinary_pigeonhole_fails :
    bestCandidateCount ≤
      baseFieldCardinality ^ 15 * productStateCount * (challengeThreshold - 1) := by
  norm_num [bestCandidateCount, baseFieldCardinality, productStateCount, challengeThreshold]

theorem minimum_trade_support_receipt :
    2 * minimumTradeSide = minimumTradeSupport := by
  norm_num [minimumTradeSide, minimumTradeSupport]

/-- At most fifteen pairwise-disjoint 34-point trade supports fit in the 510-point pool. -/
theorem disjoint_trade_count_le_fifteen
    (toggles : ℕ) (hsupport : minimumTradeSupport * toggles ≤ endpointPool) :
    toggles ≤ maximumDisjointToggles := by
  norm_num [minimumTradeSupport, endpointPool, maximumDisjointToggles] at hsupport ⊢
  omega

/-- Every cube generated by at most fifteen independent toggles is far below the challenge
threshold. -/
theorem disjoint_trade_cube_below_threshold
    (toggles : ℕ) (htoggles : toggles ≤ maximumDisjointToggles) :
    2 ^ toggles < challengeThreshold := by
  calc
    2 ^ toggles ≤ 2 ^ maximumDisjointToggles :=
      Nat.pow_le_pow_right (by norm_num) htoggles
    _ < challengeThreshold := by
      norm_num [maximumDisjointToggles, challengeThreshold]

theorem complete_dyadic_coset_ledger :
    512 / minimumMomentNullCosetOrder = maximumMomentNullCosets ∧
      2 ^ maximumMomentNullCosets = completeCosetUnionCap ∧
      completeCosetUnionCap < challengeThreshold := by
  norm_num [minimumMomentNullCosetOrder, maximumMomentNullCosets,
    completeCosetUnionCap, challengeThreshold]

theorem punctured_complete_coset_family_below_threshold :
    puncturedCosetWeight272Family = 265182525 ∧
      puncturedCosetProductFibreFloor = 517935 ∧
      puncturedCosetProductFibreFloor < challengeThreshold := by
  norm_num [puncturedCosetWeight272Family, puncturedCosetProductFibreFloor,
    challengeThreshold]

/-- Exact non-applicability receipt for the published small-`n` moment-subset estimates.  The
three inequalities are generous failures: each uses only one moment. -/
theorem published_moment_subset_hypotheses_fail_at_m_one :
    256 * subgroupPowerExponent = baseFieldCardinality - 1 ∧
      baseFieldCardinality < 2 * subgroupPowerExponent * (subgroupPowerExponent + 1) ∧
      13 ^ 2 * baseFieldCardinality < (1000 * (subgroupPowerExponent + 1)) ^ 2 ∧
      272 - 25 < 50 * subgroupPowerExponent := by
  norm_num [subgroupPowerExponent, baseFieldCardinality]

end ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

open ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

#print axioms multiset_eq_of_fifteen_coefficients_and_product
#print axioms nontrivial_trade_side_at_least_seventeen
#print axioms best_profile_ordinary_pigeonhole_fails
#print axioms disjoint_trade_cube_below_threshold
#print axioms published_moment_subset_hypotheses_fail_at_m_one
