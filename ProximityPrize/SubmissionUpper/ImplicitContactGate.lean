/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Implicit-contact gates for upper `R`-free families

The lower score-68 rectangular work routes every polynomial solution of an
`R`-free factor `A(X,Y,Z)` through the implicit contact lift
`A_X + R A_Y`.  Its proper-cut incidence ledger handles arbitrary `Y` degree
up to 127, not only the earlier linear branch.

This upper-only module records the exact ledger after substitution at both the
first agreement that would improve the promoted upper score and the prospective
square-jet endpoint.  The results are conditional rejection gates: they apply
to a family already covered by one nonzero `R`-free rectangular factor product
with the displayed coordinate-degree budgets.  They neither construct such a
family nor route derivative-dependent factors into this branch.
-/

namespace ProximityPrize.SubmissionUpper.ImplicitContactGate

def challengeThreshold : ℕ := 274980728111395088
def baseFieldCardinality : ℕ := 2130706433
def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def movingCoordinates : ℕ := domainSize - rowDegree

/-- Total `Y` degree of the rectangular factor product. -/
def yDegreeCap : ℕ := 127

/-- Total seed-coordinate degree of the rectangular factor product. -/
def seedDegreeCap : ℕ := 2958248

/-- Agreement-dependent part of the proper-cut numerator that is common to
both upper endpoints. -/
def contactDegreeCore : ℕ :=
  6 * rowDegree * yDegreeCap * seedDegreeCap + seedDegreeCap + yDegreeCap

/-- Global exceptional auxiliary cost `2*t^2`. -/
def exceptionalCap : ℕ := 2 * seedDegreeCap ^ 2

def strictImprovementAgreement : ℕ := 139776
def strictImprovementErrors : ℕ := domainSize - strictImprovementAgreement
def strictImprovementGap : ℕ := strictImprovementAgreement - rowDegree
def strictRegularNumerator : ℕ :=
  movingCoordinates * contactDegreeCore +
    (strictImprovementErrors + 1) * strictImprovementGap * yDegreeCap
def strictRegularCap : ℕ := 4448776970133290
def strictRFreeCap : ℕ := strictRegularCap + exceptionalCap

def squareJetAgreement : ℕ := 140287
def squareJetErrors : ℕ := domainSize - squareJetAgreement
def squareJetGap : ℕ := squareJetAgreement - rowDegree
def squareJetRegularNumerator : ℕ :=
  movingCoordinates * contactDegreeCore +
    (squareJetErrors + 1) * squareJetGap * yDegreeCap
def squareJetRegularCap : ℕ := 4202105418007116
def squareJetRFreeCap : ℕ := squareJetRegularCap + exceptionalCap

theorem common_arithmetic_receipt :
    movingCoordinates = 131073 ∧
      contactDegreeCore = 295458281947671 ∧
      exceptionalCap = 17502462459008 := by
  norm_num [movingCoordinates, contactDegreeCore, exceptionalCap, domainSize,
    rowDegree, yDegreeCap, seedDegreeCap]

/-- Every characteristic-sensitive coordinate and mixed degree in the
implicit-contact proper-cut argument is strictly below the benchmark prime. -/
theorem characteristic_gates :
    yDegreeCap < baseFieldCardinality ∧
      seedDegreeCap < baseFieldCardinality ∧
      2 * yDegreeCap * seedDegreeCap < baseFieldCardinality := by
  norm_num [yDegreeCap, seedDegreeCap, baseFieldCardinality]

theorem strict_endpoint_receipt :
    strictImprovementErrors = 122368 ∧
      strictImprovementGap = 8705 ∧
      strictRegularNumerator = 38726603525010293398 ∧
      strictRegularNumerator = strictRegularCap * strictImprovementGap + 3948 ∧
      strictRFreeCap = 4466279432592298 ∧
      strictRFreeCap < challengeThreshold := by
  norm_num [strictImprovementErrors, strictImprovementGap,
    strictRegularNumerator, strictRegularCap, strictRFreeCap,
    strictImprovementAgreement, movingCoordinates, contactDegreeCore,
    exceptionalCap, domainSize, rowDegree, yDegreeCap, seedDegreeCap,
    challengeThreshold]

theorem square_jet_endpoint_receipt :
    squareJetErrors = 121857 ∧
      squareJetGap = 9216 ∧
      squareJetRegularNumerator = 38726603532353583639 ∧
      squareJetRegularNumerator = squareJetRegularCap * squareJetGap + 2583 ∧
      squareJetRFreeCap = 4219607880466124 ∧
      squareJetRFreeCap < challengeThreshold := by
  norm_num [squareJetErrors, squareJetGap, squareJetRegularNumerator,
    squareJetRegularCap, squareJetRFreeCap, squareJetAgreement,
    movingCoordinates, contactDegreeCore, exceptionalCap, domainSize,
    rowDegree, yDegreeCap, seedDegreeCap, challengeThreshold]

/-- The complete arbitrary-`Y` `R`-free branch is too small even at the first
agreement that would improve the promoted upper endpoint. -/
theorem card_lt_threshold_of_strict_rfree_incidence
    (card regular exceptional : ℕ)
    (hregular : regular * strictImprovementGap ≤ strictRegularNumerator)
    (hexceptional : exceptional ≤ exceptionalCap)
    (hcover : card ≤ regular + exceptional) :
    card < challengeThreshold := by
  norm_num [strictImprovementGap, strictImprovementAgreement, rowDegree,
    strictRegularNumerator, movingCoordinates, contactDegreeCore,
    strictImprovementErrors, domainSize, yDegreeCap, seedDegreeCap,
    exceptionalCap, challengeThreshold] at hregular hexceptional hcover ⊢
  omega

/-- Sharper form of the same rejection at the prospective square-jet
agreement. -/
theorem card_lt_threshold_of_square_jet_rfree_incidence
    (card regular exceptional : ℕ)
    (hregular : regular * squareJetGap ≤ squareJetRegularNumerator)
    (hexceptional : exceptional ≤ exceptionalCap)
    (hcover : card ≤ regular + exceptional) :
    card < challengeThreshold := by
  norm_num [squareJetGap, squareJetAgreement, rowDegree,
    squareJetRegularNumerator, movingCoordinates, contactDegreeCore,
    squareJetErrors, domainSize, yDegreeCap, seedDegreeCap, exceptionalCap,
    challengeThreshold] at hregular hexceptional hcover ⊢
  omega

end ProximityPrize.SubmissionUpper.ImplicitContactGate

#print axioms ProximityPrize.SubmissionUpper.ImplicitContactGate.card_lt_threshold_of_strict_rfree_incidence
#print axioms ProximityPrize.SubmissionUpper.ImplicitContactGate.card_lt_threshold_of_square_jet_rfree_incidence
