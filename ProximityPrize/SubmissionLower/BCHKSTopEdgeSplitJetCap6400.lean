import ProximityPrize.SubmissionLower.BCHKSTopEdgeGaoMatrix6400
import ProximityPrize.SubmissionLower.BCHKSBranchwiseHybridAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTopEdgeSplitJetCap6400
open Polynomial
open BCHKSTopEdgeGaoMatrix6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSBranchwiseHybridAudit6400
def topEdgeSplitMixedJetRowCap
    {I : Type*} {nu : I -> Nat} (d : Nat) :
    TopEdgeMixedJetRowIndex I nu d -> Nat :=
  Sum.elim (fun j => d - jetLayer j) (fun j => d - 2 - jetLayer j)
theorem topEdgeMixedJetMatrix_entry_natDegree_le_split
    {F I : Type*} [Field F] [Fintype I]
    (omega : I -> F) (uZ : I -> Polynomial F) (nu : I -> Nat)
    (k d w : Nat)
    (hu : forall i, (uZ i).natDegree <= 1) :
    forall r c,
      (topEdgeMixedJetMatrix omega uZ nu k d w r c).natDegree <=
        topEdgeSplitMixedJetRowCap d r := by
  intro r c
  cases r with
  | inl j =>
      cases c with
      | inl q =>
          apply monomialMixedHasseCoefficient_natDegree_le
          · exact hu (jetPoint j)
          · have hy := q.1.1.2.isLt
            simp only [gExponentY, trapezoidY]
            omega
      | inr q => simp [topEdgeMixedJetMatrix, topEdgeSplitMixedJetRowCap]
  | inr j =>
      cases c with
      | inl q => simp [topEdgeMixedJetMatrix, topEdgeSplitMixedJetRowCap]
      | inr q =>
          apply monomialMixedHasseCoefficient_natDegree_le
          · exact hu (jetPoint j)
          · have hy := q.2.2
            simp only [hExponentY]
            omega
def topEdgeSplitBoundaryLayerCost6400 (d : Nat) : Nat :=
  2 * ∑ r ∈ Finset.range d, (185364 * r - 54293) * r
def topEdgeSplitLayerCoefficient6400 : Nat := 334539244
def topEdgeSplitAggregateJetCover6400 : Nat := 28304361817108
def topEdgeSplitSaving6400 : Nat := 806507005337
lemma topEdgeSplit_layerCost53_exact6400 :
    topEdgeSplitBoundaryLayerCost6400 53 = 17730579932 /\
      17730579932 = 53 * topEdgeSplitLayerCoefficient6400 := by
  norm_num [topEdgeSplitBoundaryLayerCost6400,
    topEdgeSplitLayerCoefficient6400, Finset.sum_range_succ]
theorem topEdgeSplitBoundaryLayerCost_le_degree53_ratio6400
    (d : Nat) (hd : d <= 53) :
    topEdgeSplitBoundaryLayerCost6400 d <=
      topEdgeSplitLayerCoefficient6400 * d := by
  interval_cases d <;>
    norm_num [topEdgeSplitBoundaryLayerCost6400,
      topEdgeSplitLayerCoefficient6400, Finset.sum_range_succ]
theorem aggregate_topEdgeSplitLayerCost_le6400
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree cheapCost : R -> Nat)
    (hdegree : ∀ r ∈ Rs, degree r <= 53)
    (hcheap : ∀ r ∈ Rs,
      cheapCost r <= topEdgeSplitBoundaryLayerCost6400 (degree r))
    (hmass : (∑ r ∈ Rs, degree r) <= 84607) :
    (∑ r ∈ Rs, cheapCost r) <= topEdgeSplitAggregateJetCover6400 := by
  calc
    (∑ r ∈ Rs, cheapCost r) <=
        ∑ r ∈ Rs, topEdgeSplitBoundaryLayerCost6400 (degree r) := by
      exact Finset.sum_le_sum hcheap
    _ <= ∑ r ∈ Rs, topEdgeSplitLayerCoefficient6400 * degree r := by
      apply Finset.sum_le_sum
      intro r hr
      exact topEdgeSplitBoundaryLayerCost_le_degree53_ratio6400
        (degree r) (hdegree r hr)
    _ = topEdgeSplitLayerCoefficient6400 * (∑ r ∈ Rs, degree r) := by
      rw [Finset.mul_sum]
    _ <= topEdgeSplitLayerCoefficient6400 * 84607 :=
      Nat.mul_le_mul_left _ hmass
    _ = topEdgeSplitAggregateJetCover6400 := by
      norm_num [topEdgeSplitLayerCoefficient6400,
        topEdgeSplitAggregateJetCover6400]
lemma topEdgeSplit_aggregate_saving_exact6400 :
    topEdgeSplitAggregateJetCover6400 =
        topEdgeSplitLayerCoefficient6400 * bchksHybridYMass6400 /\
      BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeAggregateJetCover6400 -
          topEdgeSplitAggregateJetCover6400 = topEdgeSplitSaving6400 := by
  norm_num [topEdgeSplitAggregateJetCover6400,
    topEdgeSplitLayerCoefficient6400, bchksHybridYMass6400,
    BCHKSTopEdgeMixedJetStableAudit6400.bchksTopEdgeAggregateJetCover6400,
    topEdgeSplitSaving6400]
def branchwiseSplitLowYCoefficient6400 : Nat := 334801388
def branchwiseSplitCore390Total6400 : Nat := 274979110554464891
lemma branchwiseSplit_core390_firstMiss6400 :
    branchwiseSplitLowYCoefficient6400 =
        topEdgeSplitLayerCoefficient6400 + branchwiseCoordinateCount6400 /\
      branchwiseSplitCore390Total6400 =
        branchwiseCoreFirstMissEffectiveCoefficient6400 *
            bchksHybridZMass6400 +
          branchwiseSplitLowYCoefficient6400 * bchksHybridYMass6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      bchksWeightedNumerator6400 < branchwiseSplitCore390Total6400 /\
      branchwiseSplitCore390Total6400 - bchksWeightedNumerator6400 =
        110554464891 := by
  norm_num [branchwiseSplitLowYCoefficient6400,
    topEdgeSplitLayerCoefficient6400, branchwiseCoordinateCount6400,
    branchwiseSplitCore390Total6400,
    branchwiseCoreFirstMissEffectiveCoefficient6400,
    bchksHybridZMass6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]
end BCHKSTopEdgeSplitJetCap6400
end ProximityPrize.SubmissionLower
