/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Sparse-selector Hasse gate

`HasseRankDefectGate` leaves open a selector-to-coefficient image which misses every dense
Hasse window.  The most natural such image is a lacunary locator `Q(X^g)`.  This file isolates
the exact obstruction to that escape.

At a nonzero contact, and for `g` nonzero in the field, `X \mapsto X^g` is an etale local
coordinate.  Its Jacobian is `g * x^(g-1)`, so composing with `X^g` cannot itself create a
singular tangent locus.  If `beta = x^g` still has degree two over the base field, the dense
degree-two theorem from `HasseRankDefectGate` applies in the outer `Q` coordinate and charges
sixteen base coordinates.

The only elementary coset collapse is `beta` lying in the base field.  Then every locator value
is base-field valued, and any affine challenge obtained from it by a fixed nonzero rescaling
lies on one scalar copy of the base field.  Such a line has at most `p` points, below the
benchmark challenge threshold.  Moreover, even granting this collapse, the eight positive
outer Hasse coordinates plus the seven top-coefficient pins give rank fifteen, while the exact
selector entropy permits rank at most fourteen.

Thus a viable ninth-contact construction in this chart needs a genuinely nonlinear
selector-fibre concentration: conditional Hasse rank at most seven after the seven top pins,
equivalently at least nine relations relative to the generic degree-two rank.  Physical
lacunarity alone does not provide them.  This is a scoped gate, not a score claim.
-/

namespace ProximityPrize.SubmissionUpper.SparseSelectorHasseGate

open Polynomial

variable {F : Type*} [Field F]

/-- Pull a polynomial back through the monomial chart `X \mapsto X^gap`. -/
noncomputable def monomialPullback (gap : ℕ) (Q : Polynomial F) : Polynomial F :=
  Q.comp (Polynomial.X ^ gap)

/-- The Jacobian of the monomial chart at a contact point. -/
def monomialChartJacobian (gap : ℕ) (x : F) : F :=
  (gap : F) * x ^ (gap - 1)

/-- The ordinary chain rule exposes the only possible singularities of a monomial pullback. -/
theorem monomialPullback_derivative
    (gap : ℕ) (Q : Polynomial F) :
    (monomialPullback gap Q).derivative =
      Polynomial.C (gap : F) * Polynomial.X ^ (gap - 1) *
        Q.derivative.comp (Polynomial.X ^ gap) := by
  rw [monomialPullback, Polynomial.derivative_comp, Polynomial.derivative_X_pow]

/-- Evaluation form of the chain rule. -/
theorem monomialPullback_derivative_eval
    (gap : ℕ) (Q : Polynomial F) (x : F) :
    (monomialPullback gap Q).derivative.eval x =
      monomialChartJacobian gap x * Q.derivative.eval (x ^ gap) := by
  rw [monomialPullback_derivative]
  simp [monomialChartJacobian, Polynomial.eval_mul, Polynomial.eval_comp]

/-- Below the characteristic and away from zero, the lacunary chart is not tangent-singular. -/
theorem monomialChartJacobian_ne_zero
    (gap : ℕ) (x : F) (hgap : (gap : F) ≠ 0) (hx : x ≠ 0) :
    monomialChartJacobian gap x ≠ 0 := by
  exact mul_ne_zero hgap (pow_ne_zero _ hx)

/-- Consequently a zero derivative of the pullback is exactly a zero derivative in the outer
coordinate; the exponent gap creates no new regular-point singularity. -/
theorem monomialPullback_derivative_eval_eq_zero_iff
    (gap : ℕ) (Q : Polynomial F) (x : F)
    (hgap : (gap : F) ≠ 0) (hx : x ≠ 0) :
    (monomialPullback gap Q).derivative.eval x = 0 ↔
      Q.derivative.eval (x ^ gap) = 0 := by
  rw [monomialPullback_derivative_eval]
  exact mul_eq_zero.trans (or_iff_right (monomialChartJacobian_ne_zero gap x hgap hx))

section ScalarLine

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [DecidableEq E]

/-- A scalar copy of the base field contains at most `|K|` challenges.  This is the exact image
of a one-residue lacunary locator when its outer contact `x^gap` falls into `K`. -/
theorem scalar_base_line_card_le (scale : E) :
    ((Finset.univ : Finset K).image fun c ↦ scale * algebraMap K E c).card ≤
      Fintype.card K := by
  rw [← Finset.card_univ]
  exact Finset.card_image_le

end ScalarLine

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : ℕ := 2130706433
def legalOuterDegree : ℕ := 131071
def challengeThreshold : ℕ := 274980728111395088
def canonicalSelectorCount : ℕ := Nat.choose 511 273

/-- Every legal exponent gap is nonzero in the benchmark characteristic. -/
theorem legal_gap_nonzero_mod_characteristic
    (gap : ℕ) (hpositive : 1 ≤ gap) (hlegal : gap ≤ legalOuterDegree) :
    gap % baseFieldCardinality ≠ 0 := by
  rw [Nat.mod_eq_of_lt]
  · omega
  · norm_num [legalOuterDegree, baseFieldCardinality] at hlegal ⊢
    omega

/-- A base-field challenge line is too small, while a quadratic line is large enough. -/
theorem challenge_degree_window :
    baseFieldCardinality < challengeThreshold ∧
      challengeThreshold < baseFieldCardinality ^ 2 := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- For any fixed legal gap, even granting `gap` full base-field cosets is below the challenge
threshold.  The actual fixed-contact line bound is the much smaller `p`. -/
theorem generous_legal_base_collapse_cap :
    (baseFieldCardinality - 1) * legalOuterDegree + 1 < challengeThreshold := by
  norm_num [baseFieldCardinality, legalOuterDegree, challengeThreshold]

/-- Degree and agreement ledger of the first entropy-capable ninth-contact geometry. -/
theorem canonical_ninth_contact_ledger :
    273 - 7 - 1 = 265 ∧
      265 - (1 + 9) = 255 ∧
      512 * 255 + 511 = legalOuterDegree ∧
      273 * 512 + 511 = 140287 ∧
      139782 ≤ 140287 := by
  norm_num [legalOuterDegree]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
/-- After the 512-state product key, this selector family admits fourteen base-field key
coordinates but not fifteen. -/
theorem canonical_selector_rank_window :
    512 * baseFieldCardinality ^ 14 * challengeThreshold < canonicalSelectorCount ∧
      canonicalSelectorCount <
        512 * baseFieldCardinality ^ 15 * challengeThreshold := by
  rw [canonicalSelectorCount, Nat.choose_eq_fast_choose]
  decide

/-- A quadratic contact charges sixteen positive-Hasse base coordinates.  Together with seven
top pins this is rank 23, so reaching the exact rank-14 entropy window needs nine relations. -/
theorem quadratic_rank_defect_requirement :
    8 * 2 = 16 ∧ 7 + 16 = 23 ∧ 23 - 14 = 9 := by
  norm_num

/-- The elementary base-collapse still has eight outer Hasse coordinates.  Seven top pins plus
those eight coordinates miss the exact entropy window by one complete base-field coordinate. -/
theorem collapsed_rank_still_one_too_large :
    7 + 8 = 15 ∧ 15 - 14 = 1 := by
  norm_num

#print axioms monomialPullback_derivative
#print axioms monomialPullback_derivative_eval_eq_zero_iff
#print axioms scalar_base_line_card_le
#print axioms legal_gap_nonzero_mod_characteristic
#print axioms canonical_ninth_contact_ledger
#print axioms canonical_selector_rank_window
#print axioms quadratic_rank_defect_requirement

end ProximityPrize.SubmissionUpper.SparseSelectorHasseGate
