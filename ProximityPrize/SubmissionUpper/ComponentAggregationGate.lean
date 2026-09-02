/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Component-aggregation gates for an upper attack

The upstream lower proper-cut ledger is additive over prime components.  Its
mixed node cost is even superadditive in the total component degrees, so a
canonical component owner would let one pay for all proper components with
one global degree budget.

This upper-only module verifies that algebra and substitutes the two relevant
upper agreements.  The resulting conditional caps are far below the regular
layers forced by `GlobalJetLayerGate`.  The missing premise is semantic: an
arbitrary upper family has not been assigned a unique simple component whose
specialized proper-cut eliminant is nonzero.  In particular, these theorems do
not construct an improved upper witness or assert that raw specialization
provides such an assignment.
-/

namespace ProximityPrize.SubmissionUpper.ComponentAggregationGate

def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def movingCoordinates : ℕ := domainSize - rowDegree

def componentDegreeCap : ℕ := 27

/-- The accepted rectangular seed cap plus its possible `Y` degree. -/
def seedDegreeCap : ℕ := 2958248 + 127

/-- The first jet index used in the mixed proper-node degree. -/
def jetIndex : ℕ := rowDegree + 1

/-- Mixed proper-node cost for positive component degrees `c` and `t`. -/
def mixedProperNodeCost (c t j : ℕ) : ℕ :=
  c * (1 + 2 * j * (t - 1)) + t * (2 * j * (c - 1))

/-- A subtraction-free version for positive degrees `c + 1` and `t + 1`. -/
def positiveMixedProperNodeCost (c t j : ℕ) : ℕ :=
  (c + 1) * (1 + 2 * j * t) + (t + 1) * (2 * j * c)

/-- Combining two positive degree boxes creates only nonnegative cross terms.
This is the algebraic source of the all-component aggregation saving. -/
theorem positiveMixedProperNodeCost_add
    (c₁ t₁ c₂ t₂ j : ℕ) :
    positiveMixedProperNodeCost (c₁ + c₂ + 1) (t₁ + t₂ + 1) j =
      positiveMixedProperNodeCost c₁ t₁ j +
        positiveMixedProperNodeCost c₂ t₂ j +
          4 * j * ((c₁ + 1) * (t₂ + 1) + (c₂ + 1) * (t₁ + 1)) := by
  simp [positiveMixedProperNodeCost]
  ring

theorem positiveMixedProperNodeCost_superadditive
    (c₁ t₁ c₂ t₂ j : ℕ) :
    positiveMixedProperNodeCost c₁ t₁ j +
        positiveMixedProperNodeCost c₂ t₂ j ≤
      positiveMixedProperNodeCost (c₁ + c₂ + 1) (t₁ + t₂ + 1) j := by
  rw [positiveMixedProperNodeCost_add]
  omega

def aggregateProperNodeCost : ℕ :=
  mixedProperNodeCost componentDegreeCap seedDegreeCap jetIndex

def strictAgreement : ℕ := 139776
def strictErrors : ℕ := domainSize - strictAgreement
def strictGap : ℕ := strictAgreement - rowDegree
def strictProperCutNumerator : ℕ :=
  movingCoordinates * aggregateProperNodeCost +
    (strictErrors + 1) * strictGap * seedDegreeCap
def strictProperCutCap : ℕ := 619251926952924
def strictRegularLayerGate : ℕ := 10019053654770474
def strictAggregateDegreeCeiling : ℕ := 665375101952452

def squareAgreement : ℕ := 140287
def squareErrors : ℕ := domainSize - squareAgreement
def squareGap : ℕ := squareAgreement - rowDegree
def squareProperCutNumerator : ℕ :=
  movingCoordinates * aggregateProperNodeCost +
    (squareErrors + 1) * squareGap * seedDegreeCap
def squareProperCutCap : ℕ := 584934796101070
def squareRegularLayerGate : ℕ := 10028189638182555
def squareAggregateDegreeCeiling : ℕ := 705076356855988

theorem common_arithmetic_receipt :
    movingCoordinates = 131073 ∧
      seedDegreeCap = 2958375 ∧
      jetIndex = 131072 ∧
      aggregateProperNodeCost = 41102566490139 := by
  norm_num [movingCoordinates, seedDegreeCap, jetIndex,
    aggregateProperNodeCost, mixedProperNodeCost, componentDegreeCap,
    domainSize, rowDegree]

theorem strict_endpoint_receipt :
    strictErrors = 122368 ∧
      strictGap = 8705 ∧
      strictProperCutNumerator = 5390588024125203522 ∧
      strictProperCutNumerator = strictProperCutCap * strictGap + 102 ∧
      movingCoordinates * strictAggregateDegreeCeiling +
          (strictErrors + 1) * strictGap * seedDegreeCap <
        strictRegularLayerGate * strictGap ∧
      movingCoordinates * (strictAggregateDegreeCeiling + 1) +
          (strictErrors + 1) * strictGap * seedDegreeCap ≥
        strictRegularLayerGate * strictGap := by
  norm_num [strictErrors, strictGap, strictProperCutNumerator,
    strictProperCutCap, strictAgreement, movingCoordinates,
    aggregateProperNodeCost, mixedProperNodeCost, componentDegreeCap,
    seedDegreeCap, jetIndex, strictAggregateDegreeCeiling,
    strictRegularLayerGate, domainSize, rowDegree]

theorem square_endpoint_receipt :
    squareErrors = 121857 ∧
      squareGap = 9216 ∧
      squareProperCutNumerator = 5390759080867461147 ∧
      squareProperCutNumerator = squareProperCutCap * squareGap + 27 ∧
      movingCoordinates * squareAggregateDegreeCeiling +
          (squareErrors + 1) * squareGap * seedDegreeCap <
        squareRegularLayerGate * squareGap ∧
      movingCoordinates * (squareAggregateDegreeCeiling + 1) +
          (squareErrors + 1) * squareGap * seedDegreeCap ≥
        squareRegularLayerGate * squareGap := by
  norm_num [squareErrors, squareGap, squareProperCutNumerator,
    squareProperCutCap, squareAgreement, movingCoordinates,
    aggregateProperNodeCost, mixedProperNodeCost, componentDegreeCap,
    seedDegreeCap, jetIndex, squareAggregateDegreeCeiling,
    squareRegularLayerGate, domainSize, rowDegree]

/-- A strict-endpoint layer satisfying the aggregated proper-cut incidence
ledger cannot reach the size forced by a winning cover. -/
theorem strict_layer_lt_gate_of_aggregate_degree
    (card degree : ℕ)
    (hdegree : degree ≤ strictAggregateDegreeCeiling)
    (hincidence : card * strictGap ≤
      movingCoordinates * degree +
        (strictErrors + 1) * strictGap * seedDegreeCap) :
    card < strictRegularLayerGate := by
  norm_num [strictAggregateDegreeCeiling, strictGap, strictAgreement,
    strictErrors, movingCoordinates, seedDegreeCap, strictRegularLayerGate,
    domainSize, rowDegree] at hdegree hincidence ⊢
  omega

/-- Square-jet version of the same corrected aggregation gate. -/
theorem square_layer_lt_gate_of_aggregate_degree
    (card degree : ℕ)
    (hdegree : degree ≤ squareAggregateDegreeCeiling)
    (hincidence : card * squareGap ≤
      movingCoordinates * degree +
        (squareErrors + 1) * squareGap * seedDegreeCap) :
    card < squareRegularLayerGate := by
  norm_num [squareAggregateDegreeCeiling, squareGap, squareAgreement,
    squareErrors, movingCoordinates, seedDegreeCap, squareRegularLayerGate,
    domainSize, rowDegree] at hdegree hincidence ⊢
  omega

/-- The candidate one-box mixed degree is safely inside the strict gate. -/
theorem strict_candidate_layer_lt_gate
    (card : ℕ) (hincidence : card * strictGap ≤ strictProperCutNumerator) :
    card < strictRegularLayerGate := by
  norm_num [strictGap, strictAgreement, strictProperCutNumerator,
    movingCoordinates, aggregateProperNodeCost, mixedProperNodeCost,
    componentDegreeCap, seedDegreeCap, jetIndex, strictErrors,
    strictRegularLayerGate, domainSize, rowDegree] at hincidence ⊢
  omega

/-- The candidate one-box mixed degree is safely inside the square gate. -/
theorem square_candidate_layer_lt_gate
    (card : ℕ) (hincidence : card * squareGap ≤ squareProperCutNumerator) :
    card < squareRegularLayerGate := by
  norm_num [squareGap, squareAgreement, squareProperCutNumerator,
    movingCoordinates, aggregateProperNodeCost, mixedProperNodeCost,
    componentDegreeCap, seedDegreeCap, jetIndex, squareErrors,
    squareRegularLayerGate, domainSize, rowDegree] at hincidence ⊢
  omega

#print axioms positiveMixedProperNodeCost_add
#print axioms strict_layer_lt_gate_of_aggregate_degree
#print axioms square_layer_lt_gate_of_aggregate_degree

end ProximityPrize.SubmissionUpper.ComponentAggregationGate
