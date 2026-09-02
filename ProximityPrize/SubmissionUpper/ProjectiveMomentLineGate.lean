/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Projective obstruction to packing two base-field moments into one challenge

The accepted lower construction repeatedly projects a vector space to a high-band kernel and
divides by a common factor.  A proposed upper transfer instead packs two base-field locator
moments into a quadratic-extension element and uses that element as the affine challenge.

Allowing a selector-dependent scale is the strongest elementary version of this proposal.  Its
first two high coefficients have the form

`a₀ + gamma * b₀ = scale` and
`a₁ + gamma * b₁ = scale * iota(moment)`.

If the two fixed coefficient columns are projectively independent, equal moments force equal
challenges.  Consequently an injective challenge family has at most `|K|` members, even though
the quadratic extension has `|K|²` elements.  This covers affine and projectively rescaled
parameterizations, including trace, Frobenius, or norm preprocessing only when it still produces
these fixed-column equations at the first nonconstant base-field coefficient.  If the determinant
vanishes at every such coefficient, the projective high vector is constant, so those coordinates
remain pins rather than challenge data.

The final receipts specialize the cap to the benchmark base field.  Even granting 256 disjoint
charts gives far fewer challenges than Definition 6.11 requires.

This is intentionally a fixed-affine-column gate.  It makes no assertion about selector-dependent
polynomial cofactors, nonlinear contact families, or exceptional fibres of a complement
normalization.  Those mechanisms change the coefficient columns rather than merely rescaling the
same projective point and require a separate incidence bound.
-/

namespace ProximityPrize.SubmissionUpper.ProjectiveMomentLineGate

theorem challenge_eq_of_projective_moment_eq
    {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    {a₀ a₁ b₀ b₁ gamma₁ gamma₂ scale₁ scale₂ : F} {moment₁ moment₂ : K}
    (hdet : a₀ * b₁ - a₁ * b₀ ≠ 0)
    (h₁₀ : a₀ + gamma₁ * b₀ = scale₁)
    (h₁₁ : a₁ + gamma₁ * b₁ = scale₁ * ι moment₁)
    (h₂₀ : a₀ + gamma₂ * b₀ = scale₂)
    (h₂₁ : a₁ + gamma₂ * b₁ = scale₂ * ι moment₂)
    (hmoment : moment₁ = moment₂) :
    gamma₁ = gamma₂ := by
  subst moment₂
  have hline₁ :
      a₁ + gamma₁ * b₁ = (a₀ + gamma₁ * b₀) * ι moment₁ := by
    rw [h₁₀, h₁₁]
  have hline₂ :
      a₁ + gamma₂ * b₁ = (a₀ + gamma₂ * b₀) * ι moment₁ := by
    rw [h₂₀, h₂₁]
  by_contra hgamma
  have hcoefficient : b₁ - b₀ * ι moment₁ = 0 := by
    have hproduct :
        (gamma₁ - gamma₂) * (b₁ - b₀ * ι moment₁) = 0 := by
      calc
        (gamma₁ - gamma₂) * (b₁ - b₀ * ι moment₁) =
            (a₁ + gamma₁ * b₁ - (a₀ + gamma₁ * b₀) * ι moment₁) -
              (a₁ + gamma₂ * b₁ - (a₀ + gamma₂ * b₀) * ι moment₁) := by ring
        _ = 0 := by rw [hline₁, hline₂]; ring
    exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hgamma)
  have hconstant : a₁ - a₀ * ι moment₁ = 0 := by
    calc
      a₁ - a₀ * ι moment₁ =
          (a₁ + gamma₁ * b₁ - (a₀ + gamma₁ * b₀) * ι moment₁) -
            gamma₁ * (b₁ - b₀ * ι moment₁) := by ring
      _ = 0 := by rw [hline₁, hcoefficient]; ring
  apply hdet
  calc
    a₀ * b₁ - a₁ * b₀ =
        a₀ * (b₁ - b₀ * ι moment₁) - (a₁ - a₀ * ι moment₁) * b₀ := by ring
    _ = 0 := by rw [hcoefficient, hconstant]; ring

/-- One nonconstant projective base-field coordinate caps an injectively labelled family by the
base-field cardinality.  The ambient field may be an extension of arbitrary degree. -/
theorem projective_moment_family_card_le_base
    {K F U : Type*} [Field K] [Field F] [Fintype K] [DecidableEq U]
    (ι : K →+* F) (S : Finset U) (challenge scale : U → F) (moment : U → K)
    (a₀ a₁ b₀ b₁ : F)
    (hdet : a₀ * b₁ - a₁ * b₀ ≠ 0)
    (hchallenge : Set.InjOn challenge (S : Set U))
    (h₀ : ∀ u ∈ S, a₀ + challenge u * b₀ = scale u)
    (h₁ : ∀ u ∈ S, a₁ + challenge u * b₁ = scale u * ι (moment u)) :
    S.card ≤ Fintype.card K := by
  classical
  have hmoment : Set.InjOn moment (S : Set U) := by
    intro u hu v hv huv
    apply hchallenge hu hv
    exact challenge_eq_of_projective_moment_eq ι hdet
      (h₀ u hu) (h₁ u hu) (h₀ v hv) (h₁ v hv) huv
  calc
    S.card = (S.image moment).card := (Finset.card_image_iff.mpr hmoment).symm
    _ ≤ (Finset.univ : Finset K).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card K := Finset.card_univ

def baseFieldCardinality : Nat := 2130706433
def challengeThreshold : Nat := 274980728111395088

/-- A quadratic extension has enough raw elements; its projective base-field line does not. -/
theorem quadratic_capacity_but_projective_cap_fails :
    baseFieldCardinality < challengeThreshold ∧
      challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- A rank-three `K`-linear set in a projective extension line has enough abstract points.  Thus
field reduction does not fail on raw cardinality; it fails to enter the two fixed polynomial
columns without compressing the two distinct forbidden outer degrees. -/
theorem rank_three_linear_set_raw_capacity :
    challengeThreshold <
      baseFieldCardinality ^ 2 + baseFieldCardinality + 1 := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- Even 256 separately granted projective charts remain over six orders of magnitude short. -/
theorem benchmark_256_projective_charts_below_threshold :
    256 * (baseFieldCardinality + 1) < challengeThreshold := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- The proposed `1024`-fibre geometry would improve the current agreement by 512 positions. -/
theorem benchmark_agreement_gain_receipt : 140287 - 139775 = 512 := by
  norm_num

/-- The immediate `116.12` target needs seven additional agreements, so the projective cap is a
challenge-count obstruction rather than a degree or agreement obstruction. -/
theorem benchmark_next_target_gap_receipt : 139782 - 139775 = 7 := by
  norm_num

/-- The unpinned antipodal quotient retains two separate coefficients above the legal outer cap. -/
theorem benchmark_two_forbidden_outer_degrees : 127 < 128 ∧ 127 < 130 := by
  norm_num

#print axioms challenge_eq_of_projective_moment_eq
#print axioms projective_moment_family_card_le_base
#print axioms benchmark_256_projective_charts_below_threshold

end ProximityPrize.SubmissionUpper.ProjectiveMomentLineGate
