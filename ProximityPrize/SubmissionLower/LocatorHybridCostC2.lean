/-
HYBRID SECOND-SURFACE COST — C2 VARIANT (flag level).

C2 = C1 plus the REDUCED first tail.  The first tail flag drops from

  sharpTail p   = ⟨2(padT-padY)·d, 1+(2(padY-padS)-1)·d, (2padS-1)·d⟩
to
  reducedTail p = ⟨2(padT-padY)·d, 1+2(padY-padS)·d, 2(padS-1)·d⟩ = paddedTail p d

with `d = 131072`.  The two agree on `yz + all` and on the total, and the
reduced one is smaller by `d` in the `all` column, so it is strictly `Below` the
sharp one and `flagMixed` drops.  Worth about 1.29% on the binding cells.

Everything else is inherited from C1: the coordinate is `rationalFlag`, the
moving factor is `131076 = w + 5`, the branch needs `3 ≤ p.all`, and
`ordinaryCostOf` takes the minimum against the padded two-tail cost.
-/
import ProximityPrize.SubmissionLower.LocatorHybridCostC1

namespace ProximityPrize.SubmissionLower.LocatorHybridCostC2

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- The reduced first tail at `d = 131072`; it is literally `paddedTail p 131072`. -/
def reducedTail (p : FlagDegree) : FlagDegree := paddedTail p 131072

theorem reducedTail_cumulative (p : FlagDegree) :
    (reducedTail p).all = 2 * (padS p - 1) * 131072 ∧
      middle (reducedTail p) = 1 + 2 * (padY p - 1) * 131072 ∧
      total (reducedTail p) = 1 + 2 * (padT p - 1) * 131072 :=
  paddedTail_cumulative p 131072

/-- The reduced tail is `Below` the sharp tail: same middle and total, smaller
`all` by exactly `131072`. -/
theorem reducedTail_le_sharpTail (p : FlagDegree) :
    Below (reducedTail p) (sharpTail p) := by
  have hp := reducedTail_cumulative p
  have hq := sharpTail_cumulative p
  have hb := pad_bounds p
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

theorem reducedTail_mono {p q : FlagDegree} (h : Below p q) :
    Below (reducedTail p) (reducedTail q) := by
  have hp := reducedTail_cumulative p
  have hq := reducedTail_cumulative q
  have hc := padding_mono h
  have hb := pad_bounds p
  have hb' := pad_bounds q
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  omega

/-- The C2 hybrid cost. -/
def hybridCostC2 (p : FlagDegree) : ℕ :=
  flagMixed p (reducedTail p) (hybridCoordinateC1 p) +
    131076 * flagMixed p (movingFiber p) (movingCut p)

/-- C2 never costs more than C1. -/
theorem hybridCostC2_le_hybridCostC1 (p : FlagDegree) :
    hybridCostC2 p ≤ hybridCostC1 p := by
  unfold hybridCostC2 hybridCostC1
  exact Nat.add_le_add_right
    (mixed_mono_tails p (reducedTail_le_sharpTail p)
      (⟨le_rfl, le_rfl, le_rfl⟩ : Below (hybridCoordinateC1 p)
        (hybridCoordinateC1 p))) _

/-- The hybrid branch condition, unchanged from C1. -/
def HybridAppliesC2 (p : FlagDegree) : Prop := 3 ≤ p.all ∧ p.all + 2 ≤ middle p

instance (p : FlagDegree) : Decidable (HybridAppliesC2 p) := by
  unfold HybridAppliesC2; infer_instance

def ordinaryCostOfC2 (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then
    min (hybridCostC2 p) (paddedCost 131072 131073 p)
  else paddedCost 131072 131073 p

theorem hybridCostC2_mono {p q : FlagDegree} (h : Below p q) :
    hybridCostC2 p ≤ hybridCostC2 q := by
  unfold hybridCostC2
  apply Nat.add_le_add
  · exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (reducedTail_mono h) (hybridCoordinateC1_mono h))
  · apply Nat.mul_le_mul_left
    exact (mixed_mono_first h _ _).trans
      (mixed_mono_tails q (movingFiber_mono h) (movingCut_mono h))

theorem merge_hybrid_costsC2 {I : Type*} [Fintype I]
    (p : I → FlagDegree) (P : FlagDegree)
    (hs : (∑ i, (p i).all) ≤ P.all)
    (hy : (∑ i, middle (p i)) ≤ middle P)
    (ht : (∑ i, total (p i)) ≤ total P) :
    (∑ i, (flagMixed (p i) (reducedTail P) (hybridCoordinateC1 P) +
      131076 * flagMixed (p i) (movingFiber P) (movingCut P))) ≤
      hybridCostC2 P := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold hybridCostC2
  apply Nat.add_le_add
  · exact sum_mixed_le p P _ _ hs hy ht
  · exact Nat.mul_le_mul_left _ (sum_mixed_le p P _ _ hs hy ht)

theorem hybridAppliesC2_of_below {p q : FlagDegree} (hall : p.all = q.all)
    (hpq : Below p q) (hp : HybridAppliesC2 p) : HybridAppliesC2 q := by
  obtain ⟨h1, h2⟩ := hp
  exact ⟨hall ▸ h1, by have := hpq.2.1; omega⟩

theorem ordinaryCostOfC2_le_padded (p : FlagDegree) :
    ordinaryCostOfC2 p ≤ paddedCost 131072 131073 p := by
  unfold ordinaryCostOfC2
  split_ifs
  · exact min_le_right _ _
  · exact le_rfl

def OwnBoundC2 (count : ℕ) (p : FlagDegree) : Prop :=
  count ≤ paddedCost 131072 131073 p ∧
    (HybridAppliesC2 p → count ≤ hybridCostC2 p)

theorem ownBound_le_ordinaryCostOfC2 {count : ℕ} {p : FlagDegree}
    (h : OwnBoundC2 count p) : count ≤ ordinaryCostOfC2 p := by
  unfold ordinaryCostOfC2
  split_ifs with hp
  · exact le_min (h.2 hp) h.1
  · exact h.1

theorem ownBoundC2_padded_mono {count : ℕ} {p q : FlagDegree}
    (h : Below p q) (hown : OwnBoundC2 count p) :
    count ≤ paddedCost 131072 131073 q :=
  hown.1.trans (paddedCost_mono 131072 131073 h)

end ProximityPrize.SubmissionLower.LocatorHybridCostC2
