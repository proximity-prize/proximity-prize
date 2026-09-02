/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A seed-algebra gate for large upper challenge images

The lower score-68 interpolation research suggests compressing many independent
seed sections through a low-degree relation in the seed variable.  For an
upper attack, however, the selected challenges must remain distinct.  A
nonzero univariate relation shared by all of them can therefore have degree no
smaller than the challenge image itself.

This module records that reverse-transfer obstruction.  It does not rule out
relations coupled to locator data or genuinely multivariate seed algebras.
-/

namespace ProximityPrize.SubmissionUpper.SeedAlgebraGate

/-- The inclusive selector-fibre threshold in the square-jet upper bridge. -/
def challengeThreshold : ℕ := 274980728111395088

set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 300000 in
/-- Exact endpoint receipt: `challengeThreshold` is the least integer strictly
above `2130706433 ^ 6 / 2 ^ 128`. -/
theorem challengeThreshold_receipt :
    (challengeThreshold - 1) * 2 ^ 128 < 2130706433 ^ 6 ∧
      2130706433 ^ 6 < challengeThreshold * 2 ^ 128 := by
  norm_num [challengeThreshold]

/-- A nonzero univariate polynomial that vanishes on a finite challenge set
has degree at least the cardinality of that set. -/
theorem card_le_natDegree_of_eval_eq_zero
    {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) (challenges : Finset K)
    (hP : P ≠ 0) (hzero : ∀ γ ∈ challenges, P.eval γ = 0) :
    challenges.card ≤ P.natDegree := by
  classical
  have hsubset : challenges ⊆ P.roots.toFinset := by
    intro γ hγ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hzero γ hγ
  exact (Finset.card_le_card hsubset).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))

/-- In particular, a relation on enough distinct challenges to meet the
square-jet selector threshold must itself have at least that degree. -/
theorem challengeThreshold_le_natDegree
    {K : Type*} [Field K] [DecidableEq K]
    (P : Polynomial K) (challenges : Finset K)
    (hP : P ≠ 0) (hzero : ∀ γ ∈ challenges, P.eval γ = 0)
    (hlarge : challengeThreshold ≤ challenges.card) :
    challengeThreshold ≤ P.natDegree :=
  hlarge.trans (card_le_natDegree_of_eval_eq_zero P challenges hP hzero)

end ProximityPrize.SubmissionUpper.SeedAlgebraGate

#print axioms ProximityPrize.SubmissionUpper.SeedAlgebraGate.card_le_natDegree_of_eval_eq_zero
#print axioms ProximityPrize.SubmissionUpper.SeedAlgebraGate.challengeThreshold_le_natDegree
