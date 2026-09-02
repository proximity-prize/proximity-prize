/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A two-level dyadic fixed-factor and moving-root gate

Set `Y = X^1024` and split a coarse `Y`-fibre into two `X^512` half-fibres.
The near-miss square construction suggests retaining fixed/common factors in
the outer quotient, or replacing them by a factor which moves with the one
extension-field challenge.

This file records two exact obstructions for that scoped architecture.

* A retained coarse or half-fibre factor contributes exactly as many roots as
  polynomial degrees.  It replaces fixed-core roots one-for-one, so it cannot
  improve agreement minus degree.
* If the roots of a moving factor are automatic zero agreements, they are
  roots of the affine received-word pencil `a(x) + gamma * b(x)`.  Away from
  common roots, a fixed node determines at most one challenge.  Thus at most
  `|D|` injective challenges can receive any moving root on a domain `D`.
  The benchmark threshold is vastly larger even than the full physical
  domain.

The three-point identity also shows why multiplying an affine moving factor
by an independently affine quotient does not help: in odd characteristic,
their product is affine only if one of the two moving parts vanishes.

These theorems do not rule out nonzero contact values or a nonlinear large
exceptional fibre.  They isolate the no-contact hierarchical route only.
-/

namespace ProximityPrize.SubmissionUpper.HierarchicalDyadicGate

/-- Fixed retained factors cancel from agreement minus degree.  A retained
factor may consist of any mixture of `1024`-point coarse factors and
`512`-point half-factors; only its total degree appears here. -/
theorem retained_factor_conservation
    (selected quotient retained core : ℕ) (hquotient : quotient ≤ selected) :
    selected * 1024 + retained + core =
      quotient * 1024 + retained + core + (selected - quotient) * 1024 := by
  omega

/-- The best square cell and the version with one retained half-factor have
the same degree and the same agreement. -/
theorem benchmark_retained_half_receipt :
    127 * 1024 + 1023 = 131071 ∧
      136 * 1024 + 1023 = 140287 ∧
      127 * 1024 + 512 + 511 = 131071 ∧
      136 * 1024 + 512 + 511 = 140287 := by
  norm_num

/-- Cross-multiplied quotient identity for a retained common factor.  The
right side is affine in `gamma`; at a root of `a` it is the usual quotient
agreement identity, while at a root of `common` both numerators vanish.  The
automatic agreement interpretation also requires the evaluated denominator
to be nonzero, as in the off-domain quotient construction. -/
theorem retained_common_factor_affine_identity
    {R : Type*} [CommRing R]
    (common denominator a₀ a direction quotient gamma : R)
    (hquotient : denominator * quotient = a₀ - a - gamma * direction) :
    denominator * (common * quotient) =
      common * a₀ - gamma * (common * direction) - common * a := by
  calc
    denominator * (common * quotient) =
        common * (denominator * quotient) := by ring
    _ = common * a₀ - gamma * (common * direction) - common * a := by
      rw [hquotient]
      ring

/-- For two genuinely partial half-blocks, the first three high coefficients
already fix their quadratic factor.  Here `T^2 - s*T + p` is the partial
factor and `w` is the first coefficient of the even outer factor.  The case
`s = 0` is precisely an antipodal pair and belongs to the full-block cell. -/
theorem two_partial_top_three_rigid
    {F : Type*} [Field F]
    (s p w s' p' w' : F) (hs : s ≠ 0)
    (hfirst : s = s')
    (hsecond : p + w = p' + w')
    (hthird : s * w = s' * w') :
    s = s' ∧ p = p' ∧ w = w' := by
  have hw : w = w' := by
    rw [← hfirst] at hthird
    exact mul_left_cancel₀ hs hthird
  refine ⟨hfirst, ?_, hw⟩
  rw [hw] at hsecond
  exact add_right_cancel hsecond

section AffineProduct

/-- If two affine-in-`gamma` factors have an affine product at
`gamma = 0, 1, -1`, then one factor has no moving part.  The hypothesis
`2 ≠ 0` is the only characteristic restriction. -/
theorem affine_product_three_points_forces_one_fixed
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h₀ h₁ q₀ q₁ a b : R) (htwo : (2 : R) ≠ 0)
    (hzero : h₀ * q₀ = a)
    (hone : (h₀ + h₁) * (q₀ + q₁) = a + b)
    (hneg : (h₀ - h₁) * (q₀ - q₁) = a - b) :
    h₁ = 0 ∨ q₁ = 0 := by
  have hquadratic : (2 : R) * (h₁ * q₁) = 0 := by
    linear_combination hone + hneg - 2 * hzero
  have hproduct : h₁ * q₁ = 0 :=
    (mul_eq_zero.mp hquadratic).resolve_left htwo
  exact mul_eq_zero.mp hproduct

/-- Arbitrary three-point form of the same rank-one obstruction.  It applies
to any three distinct challenges, not just a normalized `0, 1, -1` triple. -/
theorem affine_product_at_three_distinct_forces_one_fixed
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h₀ h₁ q₀ q₁ a b gamma₀ gamma₁ gamma₂ : R)
    (hgamma₀₁ : gamma₀ ≠ gamma₁)
    (hgamma₀₂ : gamma₀ ≠ gamma₂)
    (hgamma₁₂ : gamma₁ ≠ gamma₂)
    (hat₀ : (h₀ + gamma₀ * h₁) * (q₀ + gamma₀ * q₁) = a + gamma₀ * b)
    (hat₁ : (h₀ + gamma₁ * h₁) * (q₀ + gamma₁ * q₁) = a + gamma₁ * b)
    (hat₂ : (h₀ + gamma₂ * h₁) * (q₀ + gamma₂ * q₁) = a + gamma₂ * b) :
    h₁ = 0 ∨ q₁ = 0 := by
  have hdiff₀₁ :
      (gamma₀ - gamma₁) *
        (h₀ * q₁ + h₁ * q₀ - b + (gamma₀ + gamma₁) * (h₁ * q₁)) = 0 := by
    linear_combination hat₀ - hat₁
  have hdiff₀₂ :
      (gamma₀ - gamma₂) *
        (h₀ * q₁ + h₁ * q₀ - b + (gamma₀ + gamma₂) * (h₁ * q₁)) = 0 := by
    linear_combination hat₀ - hat₂
  have hsecant₀₁ :
      h₀ * q₁ + h₁ * q₀ - b + (gamma₀ + gamma₁) * (h₁ * q₁) = 0 :=
    (mul_eq_zero.mp hdiff₀₁).resolve_left (sub_ne_zero.mpr hgamma₀₁)
  have hsecant₀₂ :
      h₀ * q₁ + h₁ * q₀ - b + (gamma₀ + gamma₂) * (h₁ * q₁) = 0 :=
    (mul_eq_zero.mp hdiff₀₂).resolve_left (sub_ne_zero.mpr hgamma₀₂)
  have hquadratic : (gamma₁ - gamma₂) * (h₁ * q₁) = 0 := by
    linear_combination hsecant₀₁ - hsecant₀₂
  have hproduct : h₁ * q₁ = 0 :=
    (mul_eq_zero.mp hquadratic).resolve_left (sub_ne_zero.mpr hgamma₁₂)
  exact mul_eq_zero.mp hproduct

end AffineProduct

section MovingRoots

variable {Node F : Type*} [Field F]

/-- A noncommon root of the affine pencil on the finite domain `D`. -/
def HasMovingRoot (D : Finset Node) (a b : Node → F) (gamma : F) : Prop :=
  ∃ x ∈ D, ¬(a x = 0 ∧ b x = 0) ∧ a x + gamma * b x = 0

/-- The challenges in `Gamma` which have a noncommon root. -/
noncomputable def movingRootChallenges
    (D : Finset Node) (Gamma : Finset F) (a b : Node → F) : Finset F := by
  classical
  exact Gamma.filter (HasMovingRoot D a b)

/-- Across an injectively labelled challenge set, at most `|D|` challenges
can have even one noncommon root of an affine pencil on `D`. -/
theorem moving_root_challenges_card_le
    [DecidableEq Node] [DecidableEq F]
    (D : Finset Node) (Gamma : Finset F) (a b : Node → F) :
    (movingRootChallenges D Gamma a b).card ≤ D.card := by
  classical
  rw [movingRootChallenges]
  calc
    (Gamma.filter (HasMovingRoot D a b)).card ≤
        (D.image fun x ↦ -a x / b x).card := by
      apply Finset.card_le_card
      intro gamma hgamma
      rw [Finset.mem_filter] at hgamma
      obtain ⟨x, hx, hnoncommon, hroot⟩ := hgamma.2
      have hb : b x ≠ 0 := by
        intro hb
        apply hnoncommon
        constructor
        · rw [hb, mul_zero, add_zero] at hroot
          exact hroot
        · exact hb
      apply Finset.mem_image.mpr
      refine ⟨x, hx, ?_⟩
      symm
      apply (eq_div_iff hb).2
      linear_combination hroot
    _ ≤ D.card := Finset.card_image_le

/-- If there are more challenges than domain points, some challenge has no
noncommon affine-pencil root. -/
theorem exists_challenge_without_moving_root
    [DecidableEq Node] [DecidableEq F]
    (D : Finset Node) (Gamma : Finset F) (a b : Node → F)
    (hcard : D.card < Gamma.card) :
    ∃ gamma ∈ Gamma, ¬HasMovingRoot D a b gamma := by
  classical
  by_contra h
  have hall : ∀ gamma ∈ Gamma, HasMovingRoot D a b gamma := by
    intro gamma hgamma
    by_contra hroot
    exact h ⟨gamma, hgamma, hroot⟩
  have hsubset :
      Gamma ⊆ movingRootChallenges D Gamma a b := by
    intro gamma hgamma
    rw [movingRootChallenges, Finset.mem_filter]
    exact ⟨hgamma, hall gamma hgamma⟩
  have hlarge : Gamma.card ≤
      (movingRootChallenges D Gamma a b).card :=
    Finset.card_le_card hsubset
  have hsmall := moving_root_challenges_card_le D Gamma a b
  omega

def domainSize : ℕ := 262144
def challengeThreshold : ℕ := 274980728111395088

theorem benchmark_domain_lt_threshold : domainSize < challengeThreshold := by
  norm_num [domainSize, challengeThreshold]

/-- Even granting the moving factor the entire physical NTT domain, a
threshold-sized challenge family contains a record whose every affine-pencil
root is a common root. -/
theorem threshold_family_has_only_common_roots_for_one_challenge
    [DecidableEq Node] [DecidableEq F]
    (D : Finset Node) (Gamma : Finset F) (a b : Node → F)
    (hD : D.card ≤ domainSize)
    (hGamma : challengeThreshold ≤ Gamma.card) :
    ∃ gamma ∈ Gamma, ∀ x ∈ D,
      a x + gamma * b x = 0 → a x = 0 ∧ b x = 0 := by
  have hcard : D.card < Gamma.card := by
    exact (lt_of_le_of_lt hD benchmark_domain_lt_threshold).trans_le hGamma
  obtain ⟨gamma, hgamma, hno⟩ :=
    exists_challenge_without_moving_root D Gamma a b hcard
  refine ⟨gamma, hgamma, ?_⟩
  intro x hx hroot
  by_contra hcommon
  exact hno ⟨x, hx, hcommon, hroot⟩

end MovingRoots

#print axioms retained_factor_conservation
#print axioms retained_common_factor_affine_identity
#print axioms two_partial_top_three_rigid
#print axioms affine_product_three_points_forces_one_fixed
#print axioms affine_product_at_three_distinct_forces_one_fixed
#print axioms moving_root_challenges_card_le
#print axioms threshold_family_has_only_common_roots_for_one_challenge

end ProximityPrize.SubmissionUpper.HierarchicalDyadicGate
