/-
HYBRID SECOND-SURFACE COST — C1 VARIANT (flag level).

Differences from `LocatorHybridCost`:
  * the hybrid coordinate is the bare `rationalFlag` (the half-tail offset
    `⟨0, 65536, 196608⟩` is gone);
  * the moving term's outer factor is `131076 = w + 5` instead of `131072`;
  * `HybridApplies` requires `3 ≤ p.all` (i.e. `r ≥ 3`) rather than `2 ≤ p.all`;
  * `ordinaryCostOf` takes the MINIMUM of the hybrid and padded costs on the
    hybrid branch, so a cell can never be made worse by the branch.

`sharpTail`, `rationalFlag`, `movingFiber` and `movingCut` are reused verbatim
from `LocatorHybridCost`, together with their cumulative and monotonicity lemmas.
-/
import ProximityPrize.SubmissionLower.LocatorHybridCost

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC1

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- C1: the hybrid coordinate is the rational coordinate. -/
def hybridCoordinateC1 (p : FlagDegree) : FlagDegree := rationalFlag p

/-- The C1 hybrid cost.  `131076 = w + 5`. -/
def hybridCostC1 (p : FlagDegree) : ℕ :=
  flagMixed p (sharpTail p) (hybridCoordinateC1 p) +
    131076 * flagMixed p (movingFiber p) (movingCut p)

/-- The hybrid branch now needs slope at least `3`. -/
def HybridAppliesC1 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridAppliesC1 p) := by
  unfold HybridAppliesC1; infer_instance

/-- On the hybrid branch we may always fall back to the padded cost. -/
def ordinaryCostOfC1 (p : FlagDegree) : ℕ :=
  if HybridAppliesC1 p then
    min (hybridCostC1 p) (paddedCost 131072 131073 p)
  else paddedCost 131072 131073 p

theorem rationalFlag_cumulative (p : FlagDegree) :
    (rationalFlag p).all = 131074 * (padS p - 2) + 3 ∧
      middle (rationalFlag p) = 131074 * (padY p - 3) + 5 ∧
      total (rationalFlag p) = 131074 * (padT p - 3) + 5 := by
  have h := pad_bounds p
  dsimp only [rationalFlag, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem hybridCoordinateC1_cumulative (p : FlagDegree) :
    (hybridCoordinateC1 p).all = 131074 * (padS p - 2) + 3 ∧
      middle (hybridCoordinateC1 p) = 131074 * (padY p - 3) + 5 ∧
      total (hybridCoordinateC1 p) = 131074 * (padT p - 3) + 5 :=
  rationalFlag_cumulative p

theorem hybridCoordinateC1_mono {p q : FlagDegree} (h : Below p q) :
    Below (hybridCoordinateC1 p) (hybridCoordinateC1 q) := by
  have hp := hybridCoordinateC1_cumulative p
  have hq := hybridCoordinateC1_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem hybridCostC1_mono {p q : FlagDegree} (h : Below p q) :
    hybridCostC1 p ≤ hybridCostC1 q := by
  unfold hybridCostC1
  apply Nat.add_le_add
  · exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (sharpTail_mono h) (hybridCoordinateC1_mono h))
  · apply Nat.mul_le_mul_left
    exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (movingFiber_mono h) (movingCut_mono h))

/-- Per-factor C1 hybrid bounds at the factor's own padded tails merge into the
C1 hybrid cost of the cumulative flag. -/
theorem merge_hybrid_costsC1 {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, (flagMixed (p i) (sharpTail P) (hybridCoordinateC1 P) +
      131076 * flagMixed (p i) (movingFiber P) (movingCut P))) ≤
      hybridCostC1 P := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hybridCostC1
  apply Nat.add_le_add
  · exact sum_mixed_le p P _ _ hs hy ht
  · exact Nat.mul_le_mul_left _ (sum_mixed_le p P _ _ hs hy ht)

theorem hybridAppliesC1_of_below {p q : FlagDegree} (hall : p.all = q.all)
    (hpq : Below p q) (hp : HybridAppliesC1 p) : HybridAppliesC1 q := by
  obtain ⟨h1, h2⟩ := hp
  exact ⟨hall ▸ h1, by have := hpq.2.1; omega⟩

theorem ordinaryCostOfC1_of_hybrid (p : FlagDegree) (hp : HybridAppliesC1 p) :
    ordinaryCostOfC1 p = min (hybridCostC1 p) (paddedCost 131072 131073 p) := by
  unfold ordinaryCostOfC1
  rw [if_pos hp]

theorem ordinaryCostOfC1_of_padded (p : FlagDegree) (hp : ¬ HybridAppliesC1 p) :
    ordinaryCostOfC1 p = paddedCost 131072 131073 p := by
  unfold ordinaryCostOfC1
  rw [if_neg hp]

theorem ordinaryCostOfC1_le_padded (p : FlagDegree) :
    ordinaryCostOfC1 p ≤ paddedCost 131072 131073 p := by
  unfold ordinaryCostOfC1
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

/-- Both per-factor bounds: the padded one always, the C1 hybrid one when it
applies. -/
def OwnBoundC1 (count : ℕ) (p : FlagDegree) : Prop :=
  count ≤ paddedCost 131072 131073 p ∧
    (HybridAppliesC1 p → count ≤ hybridCostC1 p)

theorem ownBound_le_ordinaryCostOfC1 {count : ℕ} {p : FlagDegree}
    (h : OwnBoundC1 count p) : count ≤ ordinaryCostOfC1 p := by
  unfold ordinaryCostOfC1
  split_ifs with hp
  · exact le_min (h.2 hp) h.1
  · exact h.1

/-- The padded half of an `OwnBoundC1` transports along `Below`; the hybrid half
is transported by the consumer with `hybridCostC1_mono`, exactly as
`LocatorQuotientReplacement` does today (there is no monotonicity of
`ordinaryCostOf` itself across the branch boundary). -/
theorem ownBoundC1_padded_mono {count : ℕ} {p q : FlagDegree}
    (h : Below p q) (hown : OwnBoundC1 count p) :
    count ≤ paddedCost 131072 131073 q :=
  hown.1.trans (paddedCost_mono 131072 131073 h)

end ProximityPrize.SubmissionLower.LocatorHybridCostC1
