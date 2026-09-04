import ProximityPrize.SubmissionLower.LocatorFactorAggregate

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCost. -/
section PackedLocator_LocatorHybridCost

/-!
# Hybrid second-surface cost

The ordinary cost of a regular factor with cumulative flag `p` is the padded
two-tail Bezout count `paddedCost 131072 131073 p`.  When the padded slope is at
least `2` and the padded middle exceeds the padded slope by at least `2`, the
delayed second tail can be replaced by the hybrid coordinate surface, giving
`hybridCost p`, which is smaller by roughly a fifth on the binding cells.  All
tail flags are monotone in the padded cumulative degrees, so the cost is
monotone under `Below`, exactly like `paddedCost`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open scoped BigOperators
open RCN095 LocatorFactorAggregate

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- Sharp first tail `⟨2a·d, 1+(2b+1)·d, (2s+3)·d⟩` at `d = 131072`, with
`a = padT - padY`, `b = padY - padS - 1`, `s = padS - 2`. -/
def sharpTail (p : FlagDegree) : FlagDegree :=
  ⟨2 * (padT p - padY p) * 131072,
    1 + (2 * (padY p - padS p) - 1) * 131072,
    (2 * padS p - 1) * 131072⟩

def rationalFlag (p : FlagDegree) : FlagDegree :=
  ⟨131072 * (padT p - padY p) + 2 * (padT p - padY p),
    131072 * (padY p - padS p - 1) + 2 * (padY p - padS p - 1) + 2,
    131072 * (padS p - 2) + 2 * (padS p - 2) + 3⟩

def hybridCoordinate (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 65536, 196608⟩

def movingFiber (p : FlagDegree) : FlagDegree :=
  ⟨padT p - padY p, padY p - padS p, padS p + 1⟩

def movingCut (p : FlagDegree) : FlagDegree :=
  rationalFlag p + ⟨0, 131072, 262144⟩

def hybridCost (p : FlagDegree) : ℕ :=
  flagMixed p (sharpTail p) (hybridCoordinate p) +
    131072 * flagMixed p (movingFiber p) (movingCut p)

/-- The hybrid branch applies when the slope is at least `2` and the middle
exceeds the slope by at least `2`. -/
def HybridApplies (p : FlagDegree) : Prop := 2 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridApplies p) := by
  unfold HybridApplies; infer_instance

theorem pad_bounds (p : FlagDegree) :
    2 ≤ padS p ∧ padS p + 1 ≤ padY p ∧ padY p ≤ padT p :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

theorem sharpTail_cumulative (p : FlagDegree) :
    (sharpTail p).all = (2 * padS p - 1) * 131072 ∧
      middle (sharpTail p) = 1 + 2 * (padY p - 1) * 131072 ∧
      total (sharpTail p) = 1 + 2 * (padT p - 1) * 131072 := by
  have h := pad_bounds p
  dsimp only [sharpTail, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem hybridCoordinate_cumulative (p : FlagDegree) :
    (hybridCoordinate p).all = 131074 * (padS p - 2) + 196611 ∧
      middle (hybridCoordinate p) = 131074 * (padY p - 3) + 262149 ∧
      total (hybridCoordinate p) = 131074 * (padT p - 3) + 262149 := by
  have h := pad_bounds p
  dsimp only [hybridCoordinate, rationalFlag, middle, total, add_zOnly, add_yz, add_all]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingFiber_cumulative (p : FlagDegree) :
    (movingFiber p).all = padS p + 1 ∧
      middle (movingFiber p) = padY p + 1 ∧
      total (movingFiber p) = padT p + 1 := by
  have h := pad_bounds p
  dsimp only [movingFiber, middle, total]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem movingCut_cumulative (p : FlagDegree) :
    (movingCut p).all = 131074 * (padS p - 2) + 262147 ∧
      middle (movingCut p) = 131074 * (padY p - 3) + 393221 ∧
      total (movingCut p) = 131074 * (padT p - 3) + 393221 := by
  have h := pad_bounds p
  dsimp only [movingCut, rationalFlag, middle, total, add_zOnly, add_yz, add_all]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem sharpTail_mono {p q : FlagDegree} (h : Below p q) :
    Below (sharpTail p) (sharpTail q) := by
  have hp := sharpTail_cumulative p
  have hq := sharpTail_cumulative q
  have hc := padding_mono h
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem hybridCoordinate_mono {p q : FlagDegree} (h : Below p q) :
    Below (hybridCoordinate p) (hybridCoordinate q) := by
  have hp := hybridCoordinate_cumulative p
  have hq := hybridCoordinate_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem movingFiber_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingFiber p) (movingFiber q) := by
  have hp := movingFiber_cumulative p
  have hq := movingFiber_cumulative q
  have hc := padding_mono h
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem movingCut_mono {p q : FlagDegree} (h : Below p q) :
    Below (movingCut p) (movingCut q) := by
  have hp := movingCut_cumulative p
  have hq := movingCut_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem hybridCost_mono {p q : FlagDegree} (h : Below p q) :
    hybridCost p ≤ hybridCost q := by
  unfold hybridCost
  apply Nat.add_le_add
  · exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (sharpTail_mono h) (hybridCoordinate_mono h))
  · apply Nat.mul_le_mul_left
    exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (movingFiber_mono h) (movingCut_mono h))

/-- Per-factor hybrid bounds at the factor's own padded tails merge into the
hybrid cost of the cumulative flag. -/
theorem merge_hybrid_costs {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, (flagMixed (p i) (sharpTail P) (hybridCoordinate P) +
      131072 * flagMixed (p i) (movingFiber P) (movingCut P))) ≤ hybridCost P := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hybridCost
  apply Nat.add_le_add
  · exact sum_mixed_le p P _ _ hs hy ht
  · exact Nat.mul_le_mul_left _ (sum_mixed_le p P _ _ hs hy ht)

theorem hybridApplies_of_below {p q : FlagDegree} (hall : p.all = q.all)
    (hpq : Below p q) (hp : HybridApplies p) : HybridApplies q := by
  obtain ⟨h1, h2⟩ := hp
  exact ⟨hall ▸ h1, by have := hpq.2.1; omega⟩

/-! `ordinaryCostOf` and `OwnBound` are defined by `LocatorHybridCostSelect` (C2). -/

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCost

