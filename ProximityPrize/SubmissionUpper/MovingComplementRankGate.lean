/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Rank gate for affine-compatible moving complement twists

A genuinely moving complement twist need not violate the affine verifier
line.  If

`gamma * betaᵢ = etaᵢ + thetaᵢ * gamma`,

then `betaᵢ = thetaᵢ + etaᵢ / gamma` may depend nonlinearly on the challenge,
but every product `gamma * betaᵢ` seen at locator roots is still affine in
`gamma`.  With two moving coefficients, the complement pivot can involve
three base-field coordinates and therefore appears to reach the raw
rank-three projective capacity `p² + p + 1`.

The obstruction is scalar-extension rank.  The three forbidden outer
coefficients of the top quadratic-cofactor truncation form a `3 x 3` matrix
over the base field acting on `(1, beta₁, beta₂)`.  If two rows have an
invertible `beta` minor, Cramer's rule forces both moving coefficients back
to the base field.  The normalization then forces the challenge back to the
base field too.  Consequently a genuinely extension-valued construction can
live only on the rank-at-most-one locus.

The outer matrix is a Hankel matrix times a unit upper-triangular matrix.
Its rank-at-most-one locus is therefore exact: either `l₂,...,l₆` form a
geometric progression, or `l₂=...=l₅=0`.  On the generic branch the pivot
collapses to a fixed projective row line `[1,s,t]`.  There is a universal
affine moving twist for every fixed line with `t ≠ s²`, so the scalar gate
cannot close the problem: the remaining task is to bound the number of
square-free `mu_128` locators on one such line.  The case `t=s²` has zero
pivot and is impossible.  The degenerate branch has a second universal twist
after fixing its nonzero first coefficient, and likewise remains a locator
count rather than a scalar obstruction.

For one moving coefficient the exceptional equations are triangular: a
non-base twist forces four consecutive top locator coefficients to vanish.
The companion deterministic audit derives the exact outer matrix, exhausts
the complete toy model, and checks two large structured benchmark families.

This module is a standalone research gate.  It characterizes but does not
count the global rank-drop locus, and it does not change the submitted upper
certificate.
-/

namespace ProximityPrize.SubmissionUpper.MovingComplementRankGate

/-- Replacing a moving twist coefficient by
`beta = theta + eta / gamma` preserves an affine verifier word. -/
theorem moving_linear_word_is_affine
    {F : Type*} [Field F]
    (gamma beta eta theta x₀ x₁ x₂ : F)
    (hbeta : gamma * beta = eta + theta * gamma) :
    x₀ + gamma * (beta * x₁ + x₂) =
      (x₀ + eta * x₁) + gamma * (theta * x₁ + x₂) := by
  linear_combination x₁ * hbeta

/-- The same identity for two moving coefficients.  This is the exact
affine-line compatibility needed by the quadratic complement twist. -/
theorem moving_quadratic_word_is_affine
    {F : Type*} [Field F]
    (gamma beta₁ beta₂ eta₁ theta₁ eta₂ theta₂ x₀ x₁ x₂ : F)
    (hbeta₁ : gamma * beta₁ = eta₁ + theta₁ * gamma)
    (hbeta₂ : gamma * beta₂ = eta₂ + theta₂ * gamma) :
    x₀ + gamma * (beta₁ * x₁ + beta₂ * x₂) =
      (x₀ + eta₁ * x₁ + eta₂ * x₂) +
        gamma * (theta₁ * x₁ + theta₂ * x₂) := by
  linear_combination x₁ * hbeta₁ + x₂ * hbeta₂

/-- After the moving products are made affine, the complement-pivot
normalization is a projective equation in three fixed coefficient columns. -/
theorem moving_quadratic_pivot_normalization
    {F : Type*} [Field F]
    (gamma beta₁ beta₂ eta₁ theta₁ eta₂ theta₂ r₀ r₁ r₂ : F)
    (hbeta₁ : gamma * beta₁ = eta₁ + theta₁ * gamma)
    (hbeta₂ : gamma * beta₂ = eta₂ + theta₂ * gamma) :
    gamma * (r₀ + beta₁ * r₁ + beta₂ * r₂) = -1 ↔
      gamma * (r₀ + theta₁ * r₁ + theta₂ * r₂) =
        -(1 + eta₁ * r₁ + eta₂ * r₂) := by
  constructor <;> intro h
  · linear_combination h - r₁ * hbeta₁ - r₂ * hbeta₂
  · linear_combination h + r₁ * hbeta₁ + r₂ * hbeta₂

section Descent

variable {K F : Type*} [Field K] [Field F]

/-- Two independent base-field outer equations force both moving twist
coefficients to descend to the base field.  This is Cramer's rule written in
a form that does not assume the ambient extension is finite. -/
theorem two_outer_equations_force_twist_descent
    (ι : K →+* F)
    (a₀ a₁ a₂ b₀ b₁ b₂ : K) (beta₁ beta₂ : F)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ha : ι a₀ + beta₁ * ι a₁ + beta₂ * ι a₂ = 0)
    (hb : ι b₀ + beta₁ * ι b₁ + beta₂ * ι b₂ = 0) :
    beta₁ ∈ Set.range ι ∧ beta₂ ∈ Set.range ι := by
  let det := a₁ * b₂ - a₂ * b₁
  let numerator₁ := a₂ * b₀ - a₀ * b₂
  let numerator₂ := a₀ * b₁ - a₁ * b₀
  have hdet' : det ≠ 0 := by simpa only [det] using hdet
  have hmapdet : ι det ≠ 0 := (_root_.map_ne_zero ι).2 hdet'
  have hbeta₁ : beta₁ * ι det = ι numerator₁ := by
    dsimp only [det, numerator₁]
    simp only [map_sub, map_mul]
    linear_combination (ι b₂) * ha - (ι a₂) * hb
  have hbeta₂ : beta₂ * ι det = ι numerator₂ := by
    dsimp only [det, numerator₂]
    simp only [map_sub, map_mul]
    linear_combination (ι a₁) * hb - (ι b₁) * ha
  refine ⟨⟨numerator₁ / det, ?_⟩, ⟨numerator₂ / det, ?_⟩⟩
  · apply (mul_right_cancel₀ hmapdet)
    rw [hbeta₁, map_div₀, div_mul_cancel₀ _ hmapdet]
  · apply (mul_right_cancel₀ hmapdet)
    rw [hbeta₂, map_div₀, div_mul_cancel₀ _ hmapdet]

/-- Once the moving coefficients descend, a nonzero normalized pivot also
forces the challenge to descend. -/
theorem normalized_challenge_descends
    (ι : K →+* F)
    (r₀ r₁ r₂ beta₁₀ beta₂₀ : K) (gamma : F)
    (hnormalize :
      gamma * (ι r₀ + ι beta₁₀ * ι r₁ + ι beta₂₀ * ι r₂) = -1) :
    gamma ∈ Set.range ι := by
  let rho : K := r₀ + beta₁₀ * r₁ + beta₂₀ * r₂
  have hpivot : ι rho = ι r₀ + ι beta₁₀ * ι r₁ + ι beta₂₀ * ι r₂ := by
    simp only [rho, map_add, map_mul]
  have hrho : rho ≠ 0 := by
    intro hrho
    have hzero : ι rho = 0 := by rw [hrho, map_zero]
    have hbad := hnormalize
    rw [← hpivot, hzero, mul_zero] at hbad
    norm_num at hbad
  refine ⟨-rho⁻¹, ?_⟩
  have hmaprho : ι rho ≠ 0 := (_root_.map_ne_zero ι).2 hrho
  have hnorm : gamma * ι rho = -1 := by
    rw [hpivot]
    exact hnormalize
  apply (mul_right_cancel₀ hmaprho)
  calc
    ι (-rho⁻¹) * ι rho = -1 := by
      rw [map_neg, map_inv₀, neg_mul, inv_mul_cancel₀ hmaprho]
    _ = gamma * ι rho := hnorm.symm

/-- Generic rank-two outer data therefore cannot yield an extension-valued
challenge.  A viable rank-three attack must make every relevant two-row
minor vanish, leaving matrix rank at most one. -/
theorem normalized_rank_two_challenge_descends
    (ι : K →+* F)
    (a₀ a₁ a₂ b₀ b₁ b₂ r₀ r₁ r₂ : K)
    (beta₁ beta₂ gamma : F)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ha : ι a₀ + beta₁ * ι a₁ + beta₂ * ι a₂ = 0)
    (hb : ι b₀ + beta₁ * ι b₁ + beta₂ * ι b₂ = 0)
    (hnormalize : gamma * (ι r₀ + beta₁ * ι r₁ + beta₂ * ι r₂) = -1) :
    gamma ∈ Set.range ι := by
  obtain ⟨⟨beta₁₀, hbeta₁⟩, ⟨beta₂₀, hbeta₂⟩⟩ :=
    two_outer_equations_force_twist_descent ι a₀ a₁ a₂ b₀ b₁ b₂ beta₁ beta₂
      hdet ha hb
  subst beta₁
  subst beta₂
  exact normalized_challenge_descends ι r₀ r₁ r₂ beta₁₀ beta₂₀ gamma hnormalize

/-- One affine equation in a non-base element splits into its two base
components. -/
theorem nonbase_affine_eq_zero_iff
    (ι : K →+* F) (beta : F) (hbeta : beta ∉ Set.range ι) (a b : K) :
    ι a + beta * ι b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      have hιb : ι b ≠ 0 := (_root_.map_ne_zero ι).2 hb
      have hbetaEq : beta = ι (-a / b) := by
        rw [_root_.map_div₀ ι, _root_.map_neg ι]
        apply (eq_div_iff hιb).2
        linear_combination h
      exact hbeta ⟨-a / b, hbetaEq.symm⟩
    have ha : a = 0 := by
      apply ι.injective
      simpa [hb] using h
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- In the top linear-cofactor truncation, a genuinely non-base twist can
cancel degrees `66`, `65`, and `64` only when four consecutive top locator
coefficients vanish.  The three hypotheses are the exact scalar equations
derived by the companion audit. -/
theorem nonbase_linear_twist_forces_four_top_zeros
    (ι : K →+* F) (beta : F) (hbeta : beta ∉ Set.range ι)
    (l₁ l₂ l₃ l₄ l₅ : K)
    (h₂ : ι l₂ + beta * ι (l₃ - l₁ * l₂) = 0)
    (h₃ : ι l₃ + beta * ι (l₄ - l₁ * l₃) = 0)
    (h₄ : ι l₄ + beta * ι (l₅ - l₁ * l₄) = 0) :
    l₂ = 0 ∧ l₃ = 0 ∧ l₄ = 0 ∧ l₅ = 0 := by
  have hsplit₂ := (nonbase_affine_eq_zero_iff ι beta hbeta l₂
    (l₃ - l₁ * l₂)).mp h₂
  have hsplit₃ := (nonbase_affine_eq_zero_iff ι beta hbeta l₃
    (l₄ - l₁ * l₃)).mp h₃
  have hsplit₄ := (nonbase_affine_eq_zero_iff ι beta hbeta l₄
    (l₅ - l₁ * l₄)).mp h₄
  have hl₅ : l₅ = 0 := by
    linear_combination hsplit₄.2 + l₁ * hsplit₄.1
  exact ⟨hsplit₂.1, hsplit₃.1, hsplit₄.1, hl₅⟩

end Descent

/-! ## Exact rank-one outer-matrix locus -/

/-- The determinant of a `3 x 3` matrix, written without importing a matrix
library. -/
def det3
    {F : Type*} [CommRing F]
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : F) : F :=
  a₀₀ * (a₁₁ * a₂₂ - a₁₂ * a₂₁) -
    a₀₁ * (a₁₀ * a₂₂ - a₁₂ * a₂₀) +
      a₀₂ * (a₁₀ * a₂₁ - a₁₁ * a₂₀)

/-- The outer coefficient matrix is the Hankel matrix

`[[l₂,l₃,l₄],[l₃,l₄,l₅],[l₄,l₅,l₆]]`

times a unit upper-triangular matrix.  In particular, their determinants
agree.  The companion audit checks the stronger rank equality directly. -/
theorem outer_det_eq_hankel_det
    {F : Type*} [CommRing F] (l₁ l₂ l₃ l₄ l₅ l₆ : F) :
    det3 l₂ (l₃ - l₁ * l₂)
        ((l₁ ^ 2 - l₂) * l₂ - l₁ * l₃ + l₄)
      l₃ (l₄ - l₁ * l₃)
        ((l₁ ^ 2 - l₂) * l₃ - l₁ * l₄ + l₅)
      l₄ (l₅ - l₁ * l₄)
        ((l₁ ^ 2 - l₂) * l₄ - l₁ * l₅ + l₆) =
      det3 l₂ l₃ l₄ l₃ l₄ l₅ l₄ l₅ l₆ := by
  simp only [det3]
  ring

/-- Four Hankel minors give an exact case split for the rank-at-most-one
locus.  Away from `l₂ = 0`, the five coefficients `l₂,...,l₆` form a
geometric progression.  On `l₂ = 0`, rank at most one instead forces
`l₂,...,l₅` to vanish, while `l₆` remains free. -/
theorem hankel_rank_one_geometric_or_degenerate
    {F : Type*} [Field F] (l₂ l₃ l₄ l₅ l₆ : F)
    (h₄ : l₂ * l₄ = l₃ * l₃)
    (h₅ : l₂ * l₅ = l₃ * l₄)
    (h₆ : l₂ * l₆ = l₄ * l₄)
    (h₅zero : l₄ * l₆ = l₅ * l₅) :
    (l₂ = 0 ∧ l₃ = 0 ∧ l₄ = 0 ∧ l₅ = 0) ∨
      ∃ q : F, l₃ = l₂ * q ∧ l₄ = l₂ * q ^ 2 ∧
        l₅ = l₂ * q ^ 3 ∧ l₆ = l₂ * q ^ 4 := by
  letI : DecidableEq F := Classical.decEq F
  by_cases hl₂ : l₂ = 0
  · left
    have hl₃sq : l₃ * l₃ = 0 := by simpa [hl₂] using h₄.symm
    have hl₃ : l₃ = 0 := (mul_self_eq_zero.mp hl₃sq)
    have hl₄sq : l₄ * l₄ = 0 := by simpa [hl₂] using h₆.symm
    have hl₄ : l₄ = 0 := (mul_self_eq_zero.mp hl₄sq)
    have hl₅sq : l₅ * l₅ = 0 := by simpa [hl₄] using h₅zero.symm
    have hl₅ : l₅ = 0 := (mul_self_eq_zero.mp hl₅sq)
    exact ⟨hl₂, hl₃, hl₄, hl₅⟩
  · right
    let q := l₃ / l₂
    have hq : l₂ * q = l₃ := by
      dsimp only [q]
      exact mul_div_cancel₀ l₃ hl₂
    have hl₄ : l₄ = l₂ * q ^ 2 := by
      apply (mul_left_cancel₀ hl₂)
      calc
        l₂ * l₄ = l₃ * l₃ := h₄
        _ = (l₂ * q) * (l₂ * q) := by rw [hq]
        _ = l₂ * (l₂ * q ^ 2) := by ring
    have hl₅ : l₅ = l₂ * q ^ 3 := by
      apply (mul_left_cancel₀ hl₂)
      calc
        l₂ * l₅ = l₃ * l₄ := h₅
        _ = (l₂ * q) * (l₂ * q ^ 2) := by rw [hq, hl₄]
        _ = l₂ * (l₂ * q ^ 3) := by ring
    have hl₆ : l₆ = l₂ * q ^ 4 := by
      apply (mul_left_cancel₀ hl₂)
      calc
        l₂ * l₆ = l₄ * l₄ := h₆
        _ = (l₂ * q ^ 2) * (l₂ * q ^ 2) := by rw [hl₄]
        _ = l₂ * (l₂ * q ^ 4) := by ring
    exact ⟨q, hq.symm, hl₄, hl₅, hl₆⟩

/-!
For a locator with roots `U ⊆ mu_128`, let
`p_k = ∑ u∈U, u^k`.  Newton's identities translate the generic case above
to the exact Fourier-moment recurrence

`p_k = -x*p_(k-1) - l₂ * ∑_(j=2)^(k-1) q^(j-2)*p_(k-j)
       - k*l₂*q^(k-2)`

for `2 ≤ k ≤ 6`, with `p₁=-x`.  In the degenerate case,
`p_k=-x*p_(k-1)` for `2 ≤ k ≤ 5`, and
`p₆=-x*p₅-6*l₆`.  The companion audit verifies these identities against
direct sums over every toy selector, rather than treating them as merely
formal coefficient recurrences.
-/

/-- On the generic rank-one locus, normalize the surviving outer row as
`[1,s,t]`.  The high-degree equation then makes the locator coefficient
`x = l₁` cancel completely from the reciprocal pivot. -/
theorem rank_one_pivot_reduction
    {F : Type*} [CommRing F] (x s t beta₁ beta₂ : F)
    (hhigh : 1 + s * beta₁ + t * beta₂ = 0) :
    -x + beta₁ * (t - s * x - s ^ 2) +
        beta₂ * (t * (s - x) - s ^ 3) =
      (t - s ^ 2) * (beta₁ + s * beta₂) := by
  linear_combination -x * hhigh

/-- The apparent generic branch `t=s²` is actually dead: after imposing the
high equation, its reciprocal pivot is zero and cannot be normalized to
`-1`. -/
theorem rank_one_zero_discriminant_cannot_normalize
    {F : Type*} [Field F] (x s t beta₁ beta₂ gamma : F)
    (hhigh : 1 + s * beta₁ + t * beta₂ = 0)
    (ha : t - s ^ 2 = 0) :
    gamma * (-x + beta₁ * (t - s * x - s ^ 2) +
      beta₂ * (t * (s - x) - s ^ 3)) ≠ -1 := by
  have hpivot := rank_one_pivot_reduction x s t beta₁ beta₂ hhigh
  rw [ha, zero_mul] at hpivot
  intro hnormalize
  rw [hpivot, mul_zero] at hnormalize
  norm_num at hnormalize

/-- Adjoin the moving root `q=x+s` to a generic rank-one locator.  All
locators on the fixed row line `[1,s,t]` then have the same six leading
coefficients

`[-s, s²-t, 0, 0, 0, 0]`.

Equivalently, `(X-q)L` has degree `69` and its coefficients in degrees
`66,...,63` vanish.  This is the exact reduction of the remaining locator
count to a near-minimum-weight Reed--Solomon/cyclic-code problem. -/
theorem rank_one_fixed_line_augmented_prefix
    {F : Type*} [CommRing F] (x s t : F) :
    let q := x + s
    let l₂ := x ^ 2 + x * s + s ^ 2 - t
    x - q = -s ∧
      l₂ - q * x = s ^ 2 - t ∧
      l₂ * q - q * l₂ = 0 ∧
      l₂ * q ^ 2 - q * (l₂ * q) = 0 ∧
      l₂ * q ^ 3 - q * (l₂ * q ^ 2) = 0 ∧
      l₂ * q ^ 4 - q * (l₂ * q ^ 3) = 0 := by
  dsimp only
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-!
Writing `w_k = ∑_(u∈U) u^k + q^k` for the augmented root multiset,
Newton's identities applied to the fixed prefix give

`w₁=s`, `w₂=2*t-s²`, and
`w_k=s*w_(k-1)-(s²-t)*w_(k-2)` for `3 ≤ k ≤ 6`.

Thus every fixed-line fibre has the same first six augmented Fourier moments:
they are the moments of the formal quadratic alphabet with polynomial
`Z²-s*Z+(s²-t)`.  The companion audit checks this recurrence directly.
-/

/-- There is a genuine universal algebraic exception to a naive
`O(p)`-challenge count.  For any fixed `s,t` with `t ≠ s²`, the displayed
affine moving coefficients make both the normalized rank-one high equation
and pivot equation hold for every nonzero challenge `gamma`.  A complete
attack must therefore count locators on each fixed projective row line
`[1,s,t]`; scalar compatibility alone cannot close this locus. -/
theorem rank_one_universal_compatibility
    {F : Type*} [Field F] (s t gamma : F)
    (ha : t - s ^ 2 ≠ 0) (hgamma : gamma ≠ 0) :
    let a := t - s ^ 2
    let theta₁ := s / a
    let theta₂ := -1 / a
    let eta₁ := -t / a ^ 2
    let eta₂ := s / a ^ 2
    let beta₁ := theta₁ + eta₁ / gamma
    let beta₂ := theta₂ + eta₂ / gamma
    1 + s * beta₁ + t * beta₂ = 0 ∧
      gamma * a * (beta₁ + s * beta₂) = -1 := by
  dsimp only
  constructor <;> field_simp [ha, hgamma] <;> ring

/-- The degenerate rank-one branch has its own universal exception.  If
`l₂=...=l₅=0` and the sole outer equation forces `beta₂=0`, then fixing
the nonzero first coefficient `x=l₁` and taking

`beta₁ = x⁻¹ - x⁻² / gamma`

normalizes the reciprocal pivot `-x+beta₁*x²` for every nonzero challenge.
Thus this branch also reduces to a fixed-prefix locator count. -/
theorem degenerate_rank_one_universal_compatibility
    {F : Type*} [Field F] (x gamma : F) (hx : x ≠ 0) (hgamma : gamma ≠ 0) :
    let beta₁ := 1 / x - (1 / x ^ 2) / gamma
    gamma * (-x + beta₁ * x ^ 2) = -1 := by
  dsimp only
  field_simp [hx, hgamma]
  ring

/-- Eliminate the row parameter `t` from the generic high equation and
normalization.  With `deltaᵢ = gamma*betaᵢ`, every solution lies on one
quadratic equation in `gamma` for each fixed `s`. -/
theorem rank_one_eliminate_t
    {F : Type*} [CommRing F] (gamma s t delta₁ delta₂ : F)
    (hhigh : gamma + s * delta₁ + t * delta₂ = 0)
    (hnormalize : (t - s ^ 2) * (delta₁ + s * delta₂) = -1) :
    (gamma + s * delta₁ + s ^ 2 * delta₂) *
        (delta₁ + s * delta₂) - delta₂ = 0 := by
  calc
    (gamma + s * delta₁ + s ^ 2 * delta₂) *
          (delta₁ + s * delta₂) - delta₂ =
      (gamma + s * delta₁ + t * delta₂) *
          (delta₁ + s * delta₂) -
        delta₂ * ((t - s ^ 2) * (delta₁ + s * delta₂) + 1) := by
      ring
    _ = 0 := by rw [hhigh, hnormalize]; ring

/-- Expanded coefficients of the eliminated quadratic after substituting
`deltaᵢ=etaᵢ+thetaᵢ*gamma`.  The quadratic coefficient is the product of
a degree-two and a degree-one polynomial in `s`, so—apart from the vacuous
all-zero twist—only a bounded number of `s`-charts can lose the quadratic
challenge bound. -/
theorem rank_one_eliminated_quadratic_expansion
    {F : Type*} [CommRing F]
    (gamma s eta₁ theta₁ eta₂ theta₂ : F) :
    (gamma + s * (eta₁ + theta₁ * gamma) +
        s ^ 2 * (eta₂ + theta₂ * gamma)) *
        ((eta₁ + theta₁ * gamma) +
          s * (eta₂ + theta₂ * gamma)) -
      (eta₂ + theta₂ * gamma) =
    ((1 + s * theta₁ + s ^ 2 * theta₂) *
        (theta₁ + s * theta₂)) * gamma ^ 2 +
      ((1 + s * theta₁ + s ^ 2 * theta₂) *
          (eta₁ + s * eta₂) +
        s * (eta₁ + s * eta₂) * (theta₁ + s * theta₂) -
          theta₂) * gamma +
      (s * (eta₁ + s * eta₂) ^ 2 - eta₂) := by
  ring

/-- A degree-`64` gap factor followed by a nonzero cubic or quartic residual
cannot enter the rank-drop locus: when `l₅=l₆=0`, the Hankel determinant is
`-l₄³`.  This gives a symbolic obstruction to all `64+4` coset-factor
families, rather than merely an exhaustive benchmark scan. -/
theorem hankel_det_when_l₅_l₆_zero
    {F : Type*} [CommRing F] (l₂ l₃ l₄ : F) :
    det3 l₂ l₃ l₄ l₃ l₄ 0 l₄ 0 0 = -l₄ ^ 3 := by
  simp only [det3]
  ring

/-! ## Reciprocal-orbit deletion closes the fixed-line locus -/

/-- Delete one reciprocal quadratic orbit
`X²-rX+1` from a monic reciprocal locator.  If the remaining factor starts
with coefficients `b₁,b₂,b₃`, the first generic rank-one row equation
`l₃=l₂(l₁+s)` is exactly the displayed quadratic in the deleted trace
`r`.  Its linear coefficient becomes `1` when the quadratic coefficient
vanishes, so it can never be the zero polynomial. -/
theorem reciprocal_deleted_rank_one_equation
    {F : Type*} [CommRing F] (b₁ b₂ b₃ r s : F) :
    (b₃ - r * b₂ + b₁) -
        (b₂ - r * b₁ + 1) * (b₁ - r + s) =
      -b₁ * r ^ 2 + (1 + b₁ * (b₁ + s)) * r +
        (b₃ + b₁ - (b₂ + 1) * (b₁ + s)) := by
  ring

/-- The deleted reciprocal rank-one equation admits at most two distinct
traces.  This is the root-count statement used by the exact double-counting
receipt below, proved directly without invoking a polynomial root API. -/
theorem reciprocal_deleted_rank_one_at_most_two
    {F : Type*} [Field F] (b₁ b₂ b₃ s r₁ r₂ r₃ : F)
    (hr₁₂ : r₁ ≠ r₂) (hr₁₃ : r₁ ≠ r₃) (hr₂₃ : r₂ ≠ r₃)
    (h₁ : -b₁ * r₁ ^ 2 + (1 + b₁ * (b₁ + s)) * r₁ +
      (b₃ + b₁ - (b₂ + 1) * (b₁ + s)) = 0)
    (h₂ : -b₁ * r₂ ^ 2 + (1 + b₁ * (b₁ + s)) * r₂ +
      (b₃ + b₁ - (b₂ + 1) * (b₁ + s)) = 0)
    (h₃ : -b₁ * r₃ ^ 2 + (1 + b₁ * (b₁ + s)) * r₃ +
      (b₃ + b₁ - (b₂ + 1) * (b₁ + s)) = 0) : False := by
  have h₁₂product :
      (r₁ - r₂) *
        (-b₁ * (r₁ + r₂) + (1 + b₁ * (b₁ + s))) = 0 := by
    calc
      (r₁ - r₂) *
          (-b₁ * (r₁ + r₂) + (1 + b₁ * (b₁ + s))) =
        (-b₁ * r₁ ^ 2 + (1 + b₁ * (b₁ + s)) * r₁ +
          (b₃ + b₁ - (b₂ + 1) * (b₁ + s))) -
        (-b₁ * r₂ ^ 2 + (1 + b₁ * (b₁ + s)) * r₂ +
          (b₃ + b₁ - (b₂ + 1) * (b₁ + s))) := by ring
      _ = 0 := by rw [h₁, h₂]; ring
  have h₁₃product :
      (r₁ - r₃) *
        (-b₁ * (r₁ + r₃) + (1 + b₁ * (b₁ + s))) = 0 := by
    calc
      (r₁ - r₃) *
          (-b₁ * (r₁ + r₃) + (1 + b₁ * (b₁ + s))) =
        (-b₁ * r₁ ^ 2 + (1 + b₁ * (b₁ + s)) * r₁ +
          (b₃ + b₁ - (b₂ + 1) * (b₁ + s))) -
        (-b₁ * r₃ ^ 2 + (1 + b₁ * (b₁ + s)) * r₃ +
          (b₃ + b₁ - (b₂ + 1) * (b₁ + s))) := by ring
      _ = 0 := by rw [h₁, h₃]; ring
  have h₁₂ :
      -b₁ * (r₁ + r₂) + (1 + b₁ * (b₁ + s)) = 0 :=
    (mul_eq_zero.mp h₁₂product).resolve_left (sub_ne_zero.mpr hr₁₂)
  have h₁₃ :
      -b₁ * (r₁ + r₃) + (1 + b₁ * (b₁ + s)) = 0 :=
    (mul_eq_zero.mp h₁₃product).resolve_left (sub_ne_zero.mpr hr₁₃)
  have hb₁product : b₁ * (r₃ - r₂) = 0 := by
    linear_combination h₁₂ - h₁₃
  have hb₁ : b₁ = 0 :=
    (mul_eq_zero.mp hb₁product).resolve_right
      (sub_ne_zero.mpr (Ne.symm hr₂₃))
  rw [hb₁] at h₁₂
  norm_num at h₁₂

/-! ## Partial contact on one common inverse orbit -/

/-- Deleting one root from a monic selector gives an affine reconstruction
equation for every fixed contact line. -/
theorem deleted_contact_recurrence
    {F : Type*} [CommRing F]
    (c beta b r Bc Bbeta : F) :
    (c - r) * Bc - b * (beta - r) * Bbeta =
      c * Bc - b * beta * Bbeta - r * (Bc - b * Bbeta) := by
  ring

/-- If the deleted-root coefficient vanishes, the target line fixes the
contact value `B(c)`.  When `b` is nonzero it also fixes `B(beta)`; the latter
is the input to the degree-six reconstruction count in the companion audit. -/
theorem exceptional_deleted_contact_fixes_value
    {F : Type*} [CommRing F]
    (c beta b r Bc Bbeta a : F)
    (hcoefficient : Bc - b * Bbeta = 0)
    (hline : (c - r) * Bc - b * (beta - r) * Bbeta = a) :
    (c - beta) * Bc = a := by
  linear_combination hline - (beta - r) * hcoefficient

/-- At zero slope there is no exceptional deleted-root branch whenever the
contact value of the remaining factor is nonzero. -/
theorem zero_slope_deletion_coefficient_ne_zero
    {F : Type*} [Ring F] (Bc Bbeta : F) (hBc : Bc ≠ 0) :
    Bc - 0 * Bbeta ≠ 0 := by
  simpa using hBc

/-- Precise hypothesis needed for degree-six reconstruction: evaluation at
`beta` is injective on base polynomials of degree at most five.  Under this
hypothesis, the value at `beta` of a monic degree-six polynomial determines
the polynomial.  In the benchmark this follows when `beta` has degree six
over the base field. -/
theorem monic_degree_six_eq_of_eval_eq
    {K F : Type*} [Field K] [Field F]
    (ι : K →+* F) (beta : F)
    (hevalInjective : ∀ P : Polynomial K,
      P.natDegree ≤ 5 → (P.map ι).eval beta = 0 → P = 0)
    {P Q : Polynomial K}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdegree : P.natDegree = 6) (hQdegree : Q.natDegree = 6)
    (heval : (P.map ι).eval beta = (Q.map ι).eval beta) :
    P = Q := by
  have hdegree : (P - Q).natDegree ≤ 5 := by
    by_cases hzero : P - Q = 0
    · simp [hzero]
    · have hdegreeEq : P.degree = Q.degree := by
        rw [Polynomial.degree_eq_natDegree hPmonic.ne_zero,
          Polynomial.degree_eq_natDegree hQmonic.ne_zero, hPdegree, hQdegree]
      have hltDegree : (P - Q).degree < P.degree :=
        Polynomial.degree_sub_lt hdegreeEq hPmonic.ne_zero <| by
          rw [hPmonic.leadingCoeff, hQmonic.leadingCoeff]
      have hlt : (P - Q).natDegree < 6 := by
        rw [Polynomial.degree_eq_natDegree hzero,
          Polynomial.degree_eq_natDegree hPmonic.ne_zero, hPdegree] at hltDegree
        exact_mod_cast hltDegree
      omega
  have hzero : ((P - Q).map ι).eval beta = 0 := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, heval, sub_self]
  exact sub_eq_zero.mp (hevalInjective (P - Q) hdegree hzero)

/-- After 26 roots are retained, equality of the full contact value
reconstructs the deleted monic degree-six factor, provided the retained
factor is nonzero at `beta`. -/
theorem missing_degree_six_factor_eq_of_contact_eval_eq
    {K F : Type*} [Field K] [Field F]
    (ι : K →+* F) (beta : F)
    (hevalInjective : ∀ P : Polynomial K,
      P.natDegree ≤ 5 → (P.map ι).eval beta = 0 → P = 0)
    {C P Q : Polynomial K}
    (hC : (C.map ι).eval beta ≠ 0)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPdegree : P.natDegree = 6) (hQdegree : Q.natDegree = 6)
    (heval : ((C * P).map ι).eval beta = ((C * Q).map ι).eval beta) :
    P = Q := by
  have hevalPQ : (P.map ι).eval beta = (Q.map ι).eval beta := by
    apply mul_left_cancel₀ hC
    simpa only [Polynomial.map_mul, Polynomial.eval_mul] using heval
  exact monic_degree_six_eq_of_eval_eq ι beta hevalInjective hPmonic hQmonic
    hPdegree hQdegree hevalPQ

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : ℕ := 2130706433
def challengeThreshold : ℕ := 274980728111395088
def antipodalSelectorCount : ℕ :=
  8759284249504283281529408629099087875
def cosetFactorLocatorCount : ℕ := 1270752
def oneCommonInverseRecords : ℕ := 409894288378212890
def reciprocalOrbitSelectors : ℕ := 759510004936100355
def reciprocalDeletionBases : ℕ := 860778005594247069
def reciprocalGenericLineCap : ℕ := 50634000329073357
def reciprocalDegenerateLineCap : ℕ := 25317000164536678
def exceptionalDegreeSixBaseCap : ℕ := 231484530800
def contactLineFibreCap : ℕ := 13663346371740223
def forcedContactLineRecords : ℕ := 51937288981516722

/-- Rank-three projective capacity is sufficient in the abstract, while any
union of 256 descended projective lines is far too small. -/
theorem benchmark_rank_three_capacity_and_descended_cap :
    challengeThreshold <
        baseFieldCardinality ^ 2 + baseFieldCardinality + 1 ∧
      256 * (baseFieldCardinality + 1) < challengeThreshold := by
  norm_num [challengeThreshold, baseFieldCardinality]

/-- The unrestricted antipodal pool affords two base-field symbols, with a
surplus strictly between factors seven and eight, but not a third ordinary
symbol. -/
theorem benchmark_two_symbol_window :
    7 * baseFieldCardinality ^ 2 * challengeThreshold <
        antipodalSelectorCount ∧
      antipodalSelectorCount <
        8 * baseFieldCardinality ^ 2 * challengeThreshold ∧
      antipodalSelectorCount <
        baseFieldCardinality ^ 3 * challengeThreshold := by
  norm_num [baseFieldCardinality, challengeThreshold, antipodalSelectorCount]

/-- Exact deletion arithmetic for reciprocal-orbit selectors.  A fixed
generic rank-one line admits at most two reinserted traces per degree-66
base; a fixed degenerate universal line fixes `l₁` and admits at most one.
Both caps are already far below the challenge threshold. -/
theorem benchmark_reciprocal_rank_one_deletion_caps :
    reciprocalOrbitSelectors = 759510004936100355 ∧
      34 * reciprocalGenericLineCap = 2 * reciprocalDeletionBases ∧
      reciprocalGenericLineCap < challengeThreshold ∧
      34 * reciprocalDegenerateLineCap ≤ reciprocalDeletionBases ∧
      reciprocalDeletionBases < 34 * (reciprocalDegenerateLineCap + 1) ∧
      reciprocalDegenerateLineCap < challengeThreshold := by
  norm_num [reciprocalOrbitSelectors, reciprocalDeletionBases,
    reciprocalGenericLineCap, reciprocalDegenerateLineCap,
    challengeThreshold]

/-- Robust final budget for the scalar case split: even granting five
universal fixed-prefix charts at the larger generic deletion cap, plus ten
base-field-sized nonuniversal chart families, remains below the verifier's
challenge threshold.  The coefficient audit needs only three generic and two
degenerate universal charts, so this receipt has deliberate slack. -/
theorem benchmark_reciprocal_rank_one_total_budget :
    5 * reciprocalGenericLineCap + 10 * baseFieldCardinality <
      challengeThreshold := by
  norm_num [reciprocalGenericLineCap, baseFieldCardinality,
    challengeThreshold]

/-- The complete benchmark `64+4` coset-factor class checked by the companion
audit is itself much smaller than the challenge threshold. -/
theorem benchmark_coset_factor_pool_below_threshold :
    cosetFactorLocatorCount < challengeThreshold := by
  norm_num [cosetFactorLocatorCount, challengeThreshold]

/-- Exact arithmetic behind the deletion bound.  The first number is
`C(62,32) + 29 * floor(C(62,26) / C(32,6))`; division by 33 gives the sharp
integer contact-line cap. -/
theorem benchmark_contact_deletion_arithmetic :
    450883717216034179 + 29 * exceptionalDegreeSixBaseCap =
        450890430267427379 ∧
      33 * contactLineFibreCap ≤ 450890430267427379 ∧
      450890430267427379 < 33 * (contactLineFibreCap + 1) := by
  norm_num [exceptionalDegreeSixBaseCap, contactLineFibreCap]

/-- If every record needs 519 of the 4096 common-orbit contact positions,
double counting forces one fixed contact line to contain the displayed
number of records. -/
theorem benchmark_forced_contact_line_ceiling :
    4096 * (forcedContactLineRecords - 1) <
        519 * oneCommonInverseRecords ∧
      519 * oneCommonInverseRecords ≤ 4096 * forcedContactLineRecords := by
  norm_num [forcedContactLineRecords, oneCommonInverseRecords]

/-- The degree-six deletion cap is far below the line occupancy forced by
partial contact. -/
theorem benchmark_partial_contact_line_gap :
    contactLineFibreCap < forcedContactLineRecords ∧
      4096 * contactLineFibreCap < 519 * oneCommonInverseRecords := by
  norm_num [contactLineFibreCap, forcedContactLineRecords,
    oneCommonInverseRecords]

/-- Conditional combinatorial wrapper: once the deletion recurrence supplies
the per-line cap, 519 retained agreements on a 4096-point common orbit are
impossible for the entire `C(62,33)` record family. -/
theorem no_one_common_partial_contact_incidence
    (incidences : ℕ)
    (hlower : 519 * oneCommonInverseRecords ≤ incidences)
    (hupper : incidences ≤ 4096 * contactLineFibreCap) : False := by
  have hgap := benchmark_partial_contact_line_gap.2
  omega

#print axioms moving_quadratic_word_is_affine
#print axioms moving_quadratic_pivot_normalization
#print axioms two_outer_equations_force_twist_descent
#print axioms normalized_rank_two_challenge_descends
#print axioms nonbase_linear_twist_forces_four_top_zeros
#print axioms outer_det_eq_hankel_det
#print axioms hankel_rank_one_geometric_or_degenerate
#print axioms rank_one_pivot_reduction
#print axioms rank_one_zero_discriminant_cannot_normalize
#print axioms rank_one_fixed_line_augmented_prefix
#print axioms rank_one_universal_compatibility
#print axioms degenerate_rank_one_universal_compatibility
#print axioms rank_one_eliminate_t
#print axioms rank_one_eliminated_quadratic_expansion
#print axioms hankel_det_when_l₅_l₆_zero
#print axioms reciprocal_deleted_rank_one_equation
#print axioms reciprocal_deleted_rank_one_at_most_two
#print axioms benchmark_reciprocal_rank_one_deletion_caps
#print axioms benchmark_reciprocal_rank_one_total_budget
#print axioms exceptional_deleted_contact_fixes_value
#print axioms missing_degree_six_factor_eq_of_contact_eval_eq
#print axioms no_one_common_partial_contact_incidence

end ProximityPrize.SubmissionUpper.MovingComplementRankGate
