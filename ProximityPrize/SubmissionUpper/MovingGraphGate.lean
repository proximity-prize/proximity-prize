/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Moving-graph gates at the prospective square-jet endpoint

The lower score-68 rectangular-provider work proves a sharp moving-graph
incidence consumer and a global pseudodivision ledger.  This upper-only module
records their exact arithmetic after substitution of the prospective
`140287`-agreement endpoint.

The results are conditional rejection gates: they apply after a proposed
upper family has been routed to the corresponding univariate moving-graph or
`R`-free, `Y`-linear factor branch.  They do not route arbitrary families to
those branches, and in particular do not close derivative-dependent,
nonlinear, locator-coupled, or genuinely multivariate seed constructions.
-/

namespace ProximityPrize.SubmissionUpper.MovingGraphGate

/-- Inclusive upper challenge threshold `floor(2130706433^6 / 2^128) + 1`. -/
def challengeThreshold : ℕ := 274980728111395088

/-- Benchmark domain size. -/
def domainSize : ℕ := 262144

/-- Maximum degree of the fixed-domain row polynomials. -/
def rowDegree : ℕ := 131071

/-- Agreement of the prospective square-jet `115.46` endpoint. -/
def squareJetAgreement : ℕ := 140287

/-- Its unsafe index and the intrinsic cap for one affine-pencil branch. -/
def squareJetUnsafe : ℕ := 121857

/-- Independent-seed cap of the proved lower rectangular provider. -/
def rectangularSeedCap : ℕ := 2958248

/-- Number of possible `R`-free, `Y`-linear factor owners in the transferred
global pseudodivision ledger. -/
def linearFactorCap : ℕ := 127

/-- Exact agreement surplus beyond the row degree. -/
def agreementGap : ℕ := squareJetAgreement - rowDegree

/-- Exact number of coordinates outside a maximal identity set. -/
def movingCoordinates : ℕ := domainSize - rowDegree

/-- Nonidentity incidence numerator for one raw univariate moving graph. -/
def directGraphNumerator : ℕ := movingCoordinates * rectangularSeedCap

/-- The resulting direct moving-graph list cap, including the affine-pencil
alternative. -/
def directGraphCap : ℕ := 42073181

/-- Aggregate challenge-degree budget from global-sum pseudodivision. -/
def aggregateGraphDegree : ℕ :=
  (rowDegree + 1) * rectangularSeedCap + linearFactorCap

/-- Leading-degree exceptions plus one intrinsic affine-pencil cap per
possible factor owner. -/
def aggregateExceptions : ℕ :=
  2 * rectangularSeedCap + linearFactorCap * (squareJetUnsafe + 1)

/-- Complete transferred cap for the `R`-free, `Y`-linear branch. -/
def aggregateLinearCap : ℕ := 5514637431302

/-- Adding the already-closed `R`-free, `Y`-free factors costs only the
summed seed degree. -/
def aggregateRFreeLowYCap : ℕ := aggregateLinearCap + rectangularSeedCap

/-- First bivariate total degree not rejected by the elementary
`F_p^2` grid-root incidence ledger. -/
def bivariateDegreeGate : ℕ := 9074190

theorem benchmark_arithmetic_receipt :
    agreementGap = 9216 ∧ movingCoordinates = 131073 ∧
      directGraphNumerator = 387746440104 ∧
      aggregateGraphDegree = 387743481983 ∧
      aggregateExceptions = 21392462 := by
  norm_num [agreementGap, movingCoordinates, directGraphNumerator,
    aggregateGraphDegree, aggregateExceptions, squareJetAgreement, rowDegree,
    domainSize, rectangularSeedCap, linearFactorCap, squareJetUnsafe]

/-- The old score-68 weighted cap exceeds the available square-jet contact
roots by exactly `3,781,660`. -/
theorem old_rectangular_degree_deficit :
    16688064 - 92 * squareJetAgreement = 3781660 := by
  norm_num [squareJetAgreement]

/-- Retuning the old provider to the square-jet contact cap gives a negative
dimension surplus for every number of rectangular seed sections. -/
theorem retuned_rectangular_surplus_neg (z : ℕ) :
    (-2098206637940 : ℤ) - 10576756596 * z < 0 := by
  omega

/-- Exact division receipt for the direct moving-graph cap. -/
theorem directGraphCap_receipt :
    directGraphCap =
      max (squareJetUnsafe + 1) (directGraphNumerator / agreementGap) := by
  norm_num [directGraphCap, squareJetUnsafe, directGraphNumerator,
    movingCoordinates, rectangularSeedCap, agreementGap, squareJetAgreement,
    rowDegree, domainSize]

/-- Any family already satisfying the transferred univariate incidence
dichotomy is far below the inclusive upper threshold. -/
theorem card_lt_challengeThreshold_of_direct_graph
    (card : ℕ)
    (h : card ≤ squareJetUnsafe + 1 ∨
      card * agreementGap ≤ directGraphNumerator) :
    card < challengeThreshold := by
  rcases h with hpencil | hgraph
  · norm_num [squareJetUnsafe, challengeThreshold] at hpencil ⊢
    omega
  · norm_num [agreementGap, squareJetAgreement, rowDegree,
      directGraphNumerator, movingCoordinates, domainSize,
      rectangularSeedCap, challengeThreshold] at hgraph ⊢
    omega

/-- Exact floor receipt for the complete aggregate pseudodivision branch. -/
theorem aggregateLinearCap_receipt :
    aggregateLinearCap = aggregateExceptions +
      movingCoordinates * aggregateGraphDegree / agreementGap := by
  norm_num [aggregateLinearCap, aggregateExceptions, movingCoordinates,
    aggregateGraphDegree, agreementGap, rectangularSeedCap, linearFactorCap,
    squareJetUnsafe, domainSize, rowDegree, squareJetAgreement]

/-- The entire routed `R`-free, `Y`-linear branch is still strictly smaller
than the challenge threshold. -/
theorem aggregateLinearCap_lt_threshold :
    aggregateLinearCap < challengeThreshold := by
  norm_num [aggregateLinearCap, challengeThreshold]

theorem aggregateRFreeLowYCap_receipt :
    aggregateRFreeLowYCap = 5514640389550 ∧
      aggregateRFreeLowYCap < challengeThreshold := by
  norm_num [aggregateRFreeLowYCap, aggregateLinearCap, rectangularSeedCap,
    challengeThreshold]

theorem card_lt_challengeThreshold_of_aggregate_linear
    (card : ℕ) (hcard : card ≤ aggregateLinearCap) :
    card < challengeThreshold :=
  hcard.trans_lt aggregateLinearCap_lt_threshold

/-- Sharp integer endpoint for the elementary bivariate grid-root gate. -/
theorem bivariateDegreeGate_receipt :
    movingCoordinates * (bivariateDegreeGate - 1) * 2130706433 <
        challengeThreshold * agreementGap ∧
      challengeThreshold * agreementGap ≤
        movingCoordinates * bivariateDegreeGate * 2130706433 := by
  norm_num [movingCoordinates, domainSize, rowDegree, bivariateDegreeGate,
    challengeThreshold, agreementGap, squareJetAgreement]

/-- Hence any bivariate base-plane graph paid only by the elementary grid
root count needs total degree at least `9,074,190`. -/
theorem bivariateDegreeGate_le_of_incidence
    (degree : ℕ)
    (hincidence : challengeThreshold * agreementGap ≤
      movingCoordinates * degree * 2130706433) :
    bivariateDegreeGate ≤ degree := by
  norm_num [challengeThreshold, agreementGap, squareJetAgreement, rowDegree,
    movingCoordinates, domainSize, bivariateDegreeGate] at hincidence ⊢
  omega

end ProximityPrize.SubmissionUpper.MovingGraphGate

#print axioms ProximityPrize.SubmissionUpper.MovingGraphGate.card_lt_challengeThreshold_of_direct_graph
#print axioms ProximityPrize.SubmissionUpper.MovingGraphGate.card_lt_challengeThreshold_of_aggregate_linear
#print axioms ProximityPrize.SubmissionUpper.MovingGraphGate.bivariateDegreeGate_le_of_incidence
