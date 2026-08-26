import ProximityPrize.SubmissionLower.BCHKSOrderStabilityAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSTopEdgeMixedJetStableAudit6400

/-!
Corrected degree-53 top-edge mixed-jet ledger.

The old aggregate charge assigned degree `d` to every cheap mixed row.  A
row in `Y`-Hasse layer `b` only contains powers of the affine received value
up to `d-b`; writing `r=d-1-b`, its `Z`-degree is at most `r+1`.  At the
boundary profile the selected row count in that layer is `a*r-g`.  This is
the conservative bound; removing the normalized component's top `Y` term
would sharpen `r+1` to `r`, but is not needed.

Thus one factor of degree `d` costs at most

`2 * sum (r=1..d-1), (a*r-g)*(r+1)`

in cheap determinant degree.  Through degree 53, this is at most
`344071635*d`, so summing factor degrees costs only
`344071635*(DY-1)`.  This recovers enough room to include the independent
order-stability cover.

The arithmetic here does not prove the remaining sparse top-edge Gao
kernel/rank specialization theorem; it records its exact sound budget.
-/

def topEdgeBoundaryLayerCost6400 (d : ℕ) : ℕ :=
  2 * ∑ r ∈ Finset.range d, (185364 * r - 54293) * (r + 1)

def bchksTopEdgeDegree6400 : ℕ := 53
def bchksTopEdgeWeight6400 : ℕ := 9769998
def bchksTopEdgeColumns6400 : ℕ := 667441401
def bchksTopEdgeJetRankOneComponent6400 : ℕ := 252608356
def bchksTopEdgeExpensiveRows6400 : ℕ := 162224689
def bchksTopEdgeLayerCoefficient6400 : ℕ := 344071635
def bchksTopEdgeAggregateJetCover6400 : ℕ := 29110868822445
def bchksTopEdgeExpensiveCover6400 : ℕ := 273993513535941892
def bchksTopEdgeMinorCover6400 : ℕ := 274022624404764337
def bchksTopEdgePreStabilityCover6400 : ℕ := 274529800080136745
def bchksTopEdgeStableTotalCover6400 : ℕ := 274972577033951785

lemma bchksTopEdge_layerCost53_exact6400 :
    topEdgeBoundaryLayerCost6400 53 = 18235796644 ∧
      18235796644 ≤ 53 * bchksTopEdgeLayerCoefficient6400 := by
  norm_num [topEdgeBoundaryLayerCost6400,
    bchksTopEdgeLayerCoefficient6400, Finset.sum_range_succ]

/-- The layer-sensitive cost per unit factor degree is maximal at the
degree-53 endpoint. -/
theorem topEdgeBoundaryLayerCost_le_degree53_ratio6400
    (d : ℕ) (hd : d ≤ 53) :
    topEdgeBoundaryLayerCost6400 d ≤
      bchksTopEdgeLayerCoefficient6400 * d := by
  interval_cases d <;>
    norm_num [topEdgeBoundaryLayerCost6400,
      bchksTopEdgeLayerCoefficient6400, Finset.sum_range_succ]

/-- Factor-aggregate form of the corrected cheap-row ledger. -/
theorem aggregate_topEdgeLayerCost_le6400
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree cheapCost : R → ℕ)
    (hdegree : ∀ r ∈ Rs, degree r ≤ 53)
    (hcheap : ∀ r ∈ Rs,
      cheapCost r ≤ topEdgeBoundaryLayerCost6400 (degree r))
    (hmass : (∑ r ∈ Rs, degree r) ≤ 84607) :
    (∑ r ∈ Rs, cheapCost r) ≤
      bchksTopEdgeAggregateJetCover6400 := by
  calc
    (∑ r ∈ Rs, cheapCost r) ≤
        ∑ r ∈ Rs, topEdgeBoundaryLayerCost6400 (degree r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hcheap r hr
    _ ≤ ∑ r ∈ Rs,
        bchksTopEdgeLayerCoefficient6400 * degree r := by
      apply Finset.sum_le_sum
      intro r hr
      exact topEdgeBoundaryLayerCost_le_degree53_ratio6400
        (degree r) (hdegree r hr)
    _ = bchksTopEdgeLayerCoefficient6400 *
        (∑ r ∈ Rs, degree r) := by
      rw [Finset.mul_sum]
    _ ≤ bchksTopEdgeLayerCoefficient6400 * 84607 :=
      Nat.mul_le_mul_left _ hmass
    _ = bchksTopEdgeAggregateJetCover6400 := by
      norm_num [bchksTopEdgeLayerCoefficient6400,
        bchksTopEdgeAggregateJetCover6400]

lemma bchksTopEdge_exactLedger6400 :
    bchksTopEdgeWeight6400 = 53 * 185364 - 54293 - 1 ∧
      bchksTopEdgeJetRankOneComponent6400 =
        185364 * (53 * 52 / 2) - 54293 * 52 ∧
      bchksTopEdgeExpensiveRows6400 =
        bchksTopEdgeColumns6400 -
          2 * bchksTopEdgeJetRankOneComponent6400 ∧
      bchksTopEdgeAggregateJetCover6400 =
        bchksTopEdgeLayerCoefficient6400 * (84608 - 1) ∧
      bchksTopEdgeExpensiveCover6400 =
        bchksTopEdgeExpensiveRows6400 * (1688975429 - 1) ∧
      bchksTopEdgeMinorCover6400 =
        bchksTopEdgeExpensiveCover6400 +
          bchksTopEdgeAggregateJetCover6400 ∧
      bchksTopEdgePreStabilityCover6400 =
        bchksTopEdgeMinorCover6400 + 285798288073592 +
          221377387298816 ∧
      bchksTopEdgeStableTotalCover6400 =
        bchksTopEdgePreStabilityCover6400 +
          BCHKSOrderStabilityAudit6400.bchksOrderStabilityCover6400 := by
  norm_num [bchksTopEdgeWeight6400,
    bchksTopEdgeJetRankOneComponent6400, bchksTopEdgeExpensiveRows6400,
    bchksTopEdgeColumns6400, bchksTopEdgeAggregateJetCover6400,
    bchksTopEdgeLayerCoefficient6400, bchksTopEdgeExpensiveCover6400,
    bchksTopEdgeMinorCover6400, bchksTopEdgePreStabilityCover6400,
    bchksTopEdgeStableTotalCover6400,
    BCHKSOrderStabilityAudit6400.bchksOrderStabilityCover6400]

lemma bchksTopEdgeStable_fieldBudget6400 :
    bchksTopEdgeStableTotalCover6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksTopEdgeStableTotalCover6400 =
        6422966048215 ∧
      2 ^ (128 : ℕ) *
          (bchksTopEdgeStableTotalCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 ∧
      (2 * 53 - 1) * bchksTopEdgeWeight6400 < 2130706433 := by
  norm_num [bchksTopEdgeStableTotalCover6400,
    bchksWeightedNumerator6400, bchksListBound6400,
    bchksTopEdgeWeight6400]

end BCHKSTopEdgeMixedJetStableAudit6400
end ProximityPrize.SubmissionLower
