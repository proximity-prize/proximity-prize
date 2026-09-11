import ProximityPrize.SubmissionLower.Part.G001_01
section Compact_PackedLocatorTail
section PackedLocator_LocatorTwoFactorAvoidance
namespace ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorDoubleSquareAvoidance LocatorArbitraryPowerAvoidance
  LocatorArbitraryPowerContact
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid


/-- A directed helper after removing one outer copy of each factor.  For the
`F` direction the original source is `F^(j+1) * (G * J)`.  Consequently the
derivative argument makes `J` vanish on the `F`-regular seeds away from the
collision locus `G = 0`; the collision locus itself can use `G` as its cut.
-/
def HasDirectedOuterStage [AddCommMonoid V] [Module K V]
    (fuel D w delta T YS S : ℕ)
    (q : V →ₗ[K] P4 K) (F G : P4 K) : Prop :=
  ∃ (j : Fin fuel) (v : V) (J : P4 K),
    v ≠ 0 ∧ J ≠ 0 ∧ F ^ (j.val + 1) * (G * J) = q v ∧
    wt residualTotalWeights J ≤
      T - wt residualTotalWeights F - wt residualTotalWeights G -
        j.val * wt residualTotalWeights F ∧
    wt residualYSWeights J ≤
      YS - wt residualYSWeights F - wt residualYSWeights G -
        j.val * wt residualYSWeights F ∧
    wt residualSWeights J ≤
      S - wt residualSWeights F - wt residualSWeights G -
        j.val * wt residualSWeights F ∧
    wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j.val * delta - j.val * wt (contactWeights w) F ∧
    (j.val + 1 < fuel → ¬ F ∣ J)


/-- After extracting the `F`-power term, the residual helper vanishes away
from the collision with `G`.  This is the exact soundness interface needed by
the directed consumer: collision seeds are charged using `G`, and every other
`F`-regular seed is charged using `J`. -/
theorem specialization_eq_zero_of_iteratePderivR_twoFactor_offCollision
    (j : ℕ) (P : Polynomial K) (gamma : K) (F G J : P4 K)
    (hfactorial : (j.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGnonzero : RCN319.specialization K P gamma G ≠ 0)
    (hpower : RCN319.specialization K P gamma
      (iteratePderivR j (F ^ j * (G * J))) = 0) :
    RCN319.specialization K P gamma J = 0 := by
  have hGJ := specialization_eq_zero_of_iteratePderivR_power_product
    j P gamma F (G * J) hfactorial hFzero hregular hpower
  have hmul : RCN319.specialization K P gamma G *
      RCN319.specialization K P gamma J = 0 := by
    simpa only [map_mul] using hGJ
  exact (mul_eq_zero.mp hmul).resolve_left hGnonzero

private theorem reconstruct_mem_low_of_directed_power
    {I : Type} [Fintype I]
    (D w L S m delta j : ℕ) (nodes : I → K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L S m nodes u0 u1)
    (F G J : P4 K)
    (heq : F ^ (j + 1) * (G * J) =
      reconstruct K D w L S v.1)
    (hD : 0 < D) (hlowpos : 0 < D - (j + 1) * delta)
    (hcontact : wt (contactWeights w) J <
      D - delta - wt (contactWeights w) F - wt (contactWeights w) G -
        j * delta - j * wt (contactWeights w) F) :
    reconstruct K D w L S v.1 ∈
      globalCoefficientBox K (D - (j + 1) * delta) w L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) D w L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D w L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D w L S v.1) (D - (j + 1) * delta) w L S
      hlowpos).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have houter := wt_mul_le (contactWeights w) (F ^ (j + 1)) (G * J)
  have hpow := wt_pow_le (contactWeights w) F (j + 1)
  have hinner := wt_mul_le (contactWeights w) G J
  simp only [Nat.add_mul, one_mul] at hpow ⊢
  omega


end

end ProximityPrize.SubmissionLower.LocatorTwoFactorAvoidance
end PackedLocator_LocatorTwoFactorAvoidance

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorFactorAggregate. -/
section PackedLocator_LocatorFactorAggregate
namespace ProximityPrize.SubmissionLower.LocatorFactorAggregate
open scoped BigOperators
open RCN095
set_option maxRecDepth 2048
set_option maxHeartbeats 300000
def middle (p:FlagDegree):ℕ:=p.yz + p.all
def total (p:FlagDegree):ℕ:=p.zOnly + p.yz + p.all
def Below (p q:FlagDegree):Prop :=
  p.all ≤ q.all ∧ middle p ≤ middle q ∧ total p ≤ total q
def cap (t y s:ℕ):FlagDegree:=⟨t - y, y - s, s⟩
theorem mixed_expansion (p q r:FlagDegree) :
    flagMixed p q r =
      (q.all * r.all + q.yz * r.all + q.all * r.yz) * total p +
      (q.zOnly * r.all + q.all * r.zOnly) * middle p +
      (q.yz * r.yz + q.zOnly * r.yz + q.yz * r.zOnly) * p.all:=by
  simp only [flagMixed, middle, total]
  ring
theorem mixed_mono_first {p P:FlagDegree} (h:Below p P) (q r:FlagDegree) :
    flagMixed p q r ≤ flagMixed P q r:=by
  rw [mixed_expansion p q r, mixed_expansion P q r]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ h.2.2) (Nat.mul_le_mul_left _ h.2.1))
    (Nat.mul_le_mul_left _ h.1)
theorem mixed_mono_second (p:FlagDegree) {q Q:FlagDegree}
    (h:Below q Q) (r:FlagDegree):flagMixed p q r ≤ flagMixed p Q r:=by
  calc
    flagMixed p q r = flagMixed q p r:=by unfold flagMixed; ring
    _ ≤ flagMixed Q p r:=mixed_mono_first h p r
    _ = flagMixed p Q r:=by unfold flagMixed; ring
theorem mixed_mono_third (p q:FlagDegree) {r R:FlagDegree}
    (h:Below r R):flagMixed p q r ≤ flagMixed p q R:=by
  calc
    flagMixed p q r = flagMixed r q p:=by unfold flagMixed; ring
    _ ≤ flagMixed R q p:=mixed_mono_first h q p
    _ = flagMixed p q R:=by unfold flagMixed; ring
theorem mixed_mono_tails (p:FlagDegree) {q Q r R:FlagDegree}
    (hq:Below q Q) (hr:Below r R):flagMixed p q r ≤ flagMixed p Q R :=
  (mixed_mono_second p hq r).trans (mixed_mono_third p Q hr)
theorem sum_mixed_le {I:Type*} [Fintype I]
    (p:I → FlagDegree) (P q r:FlagDegree)
    (hs:(∑ i, (p i).all) ≤ P.all)
    (hy:(∑ i, middle (p i)) ≤ middle P)
    (ht:(∑ i, total (p i)) ≤ total P) :
    (∑ i, flagMixed (p i) q r) ≤ flagMixed P q r:=by
  rw [Finset.sum_congr rfl (fun i _ => mixed_expansion (p i) q r),
    mixed_expansion P q r]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hy))
    (Nat.mul_le_mul_left _ hs)
def padS (p:FlagDegree):ℕ:=max p.all 2
def padY (p:FlagDegree):ℕ:=max (middle p) (padS p + 1)
def padT (p:FlagDegree):ℕ:=max (total p) (padY p)
def paddedTail (p:FlagDegree) (d:ℕ):FlagDegree :=
  ⟨2 * (padT p - padY p) * d,
    1 + 2 * (padY p - padS p) * d,
    2 * (padS p - 1) * d⟩
def paddedCost (d e:ℕ) (p:FlagDegree):ℕ :=
  flagMixed p (paddedTail p d) (paddedTail p e)
theorem paddedTail_cumulative (p:FlagDegree) (d:ℕ) :
    (paddedTail p d).all = 2 * (padS p - 1) * d ∧
    middle (paddedTail p d) = 1 + 2 * (padY p - 1) * d ∧
    total (paddedTail p d) = 1 + 2 * (padT p - 1) * d:=by
  have hs:1 ≤ padS p:=by
    have h:2 ≤ padS p:=le_max_right _ _
    omega
  have hy:padS p + 1 ≤ padY p:=le_max_right _ _
  have ht:padY p ≤ padT p:=le_max_right _ _
  have hyadd:padY p - padS p + (padS p - 1) = padY p - 1:=by omega
  have htadd:padT p - padY p + (padY p - padS p) + (padS p - 1) =
      padT p - 1:=by omega
  refine ⟨rfl, ?_, ?_⟩
  · change (1 + 2 * (padY p - padS p) * d) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padY p - padS p + (padS p - 1)) * d:=by ring
      _ = _:=by rw [hyadd]
  · change (2 * (padT p - padY p) * d +
      (1 + 2 * (padY p - padS p) * d)) + 2 * (padS p - 1) * d = _
    calc
      _ = 1 + 2 * (padT p - padY p + (padY p - padS p) +
        (padS p - 1)) * d:=by ring
      _ = _:=by rw [htadd]
theorem padding_mono {p q:FlagDegree} (h:Below p q) :
    padS p ≤ padS q ∧ padY p ≤ padY q ∧ padT p ≤ padT q:=by
  have hs:padS p ≤ padS q:=max_le_max h.1 (Nat.le_refl 2)
  have hy:padY p ≤ padY q:=max_le_max h.2.1 (Nat.add_le_add_right hs 1)
  have ht:padT p ≤ padT q:=max_le_max h.2.2 hy
  exact ⟨hs, hy, ht⟩
theorem paddedTail_mono (d:ℕ) {p q:FlagDegree} (h:Below p q) :
    Below (paddedTail p d) (paddedTail q d):=by
  have hp:=paddedTail_cumulative p d
  have hq:=paddedTail_cumulative q d
  have hc:=padding_mono h
  have hm {a b:ℕ} (hab:a ≤ b):2 * (a - 1) * d ≤ 2 * (b - 1) * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hab 1))
  unfold Below
  rw [hp.1, hp.2.1, hp.2.2, hq.1, hq.2.1, hq.2.2]
  exact ⟨hm hc.1, Nat.add_le_add_left (hm hc.2.1) 1,
    Nat.add_le_add_left (hm hc.2.2) 1⟩
theorem paddedCost_mono (d e:ℕ) {p q:FlagDegree} (h:Below p q) :
    paddedCost d e p ≤ paddedCost d e q:=by
  exact (mixed_mono_first h _ _).trans
    (mixed_mono_tails q (paddedTail_mono d h) (paddedTail_mono e h))
private abbrev lowCap6751:ℕ:=261420997282933785
theorem all_le_middle (p:FlagDegree):p.all ≤ middle p:=by
  dsimp [middle]
  omega
theorem middle_le_total (p:FlagDegree):middle p ≤ total p:=by
  dsimp [middle, total]
  omega
private def diagonalRate (u s:ℕ):ℕ :=
  flagMixed ⟨0, 0, 1⟩
    (paddedTail (cap u u s) 131072)
    (paddedTail (cap u u s) 131073)
end ProximityPrize.SubmissionLower.LocatorFactorAggregate
end PackedLocator_LocatorFactorAggregate

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

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




/-! `ordinaryCostOf` and `OwnBound` are defined by `LocatorHybridCostSelect` (C2). -/

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCost

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostC1. -/
section PackedLocator_LocatorHybridCostC1
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






/-- Both per-factor bounds: the padded one always, the C1 hybrid one when it
applies. -/
def OwnBoundC1 (count : ℕ) (p : FlagDegree) : Prop :=
  count ≤ paddedCost 131072 131073 p ∧
    (HybridAppliesC1 p → count ≤ hybridCostC1 p)



end ProximityPrize.SubmissionLower.LocatorHybridCostC1
end PackedLocator_LocatorHybridCostC1

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostC2. -/
section PackedLocator_LocatorHybridCostC2
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



def OwnBoundC2 (count : ℕ) (p : FlagDegree) : Prop :=
  count ≤ paddedCost 131072 131073 p ∧
    (HybridAppliesC2 p → count ≤ hybridCostC2 p)



end ProximityPrize.SubmissionLower.LocatorHybridCostC2
end PackedLocator_LocatorHybridCostC2

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridCostSelect. -/
section PackedLocator_LocatorHybridCostSelect
/-!
# The ordinary cost of the 6800 certificate (C2 selection)

`LocatorHybridCost.ordinaryCostOf` is the C2 hybrid cost on the C2 branch
(`3 ≤ slope` and `slope + 2 ≤ middle`) and the padded two-tail cost otherwise.
There is deliberately no `min` against the padded cost: on the narrow box
`hybridCostC2 ≤ paddedCost 131072 131073` holds pointwise, and the `if` shape
is what `LocatorOrdinaryZConvex` needs (affine in `z`, not merely concave).
`OwnBound` is `OwnBoundC2`, produced by `LocatorFixedOwnBoundC2`.
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridCost

open RCN095 LocatorFactorAggregate LocatorHybridCostC2

def ordinaryCostOf (p : FlagDegree) : ℕ :=
  if HybridAppliesC2 p then hybridCostC2 p else paddedCost 131072 131073 p



/-- The per-factor own bound consumed by the batch and bridge modules. -/
abbrev OwnBound (count : ℕ) (p : FlagDegree) : Prop := OwnBoundC2 count p

theorem ownBound_le_ordinaryCostOf {count : ℕ} {p : FlagDegree} (h : OwnBound count p) :
    count ≤ ordinaryCostOf p := by
  unfold ordinaryCostOf
  split_ifs with hp
  · exact h.2 hp
  · exact h.1

end ProximityPrize.SubmissionLower.LocatorHybridCost
end PackedLocator_LocatorHybridCostSelect

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorBatchProductRoute. -/
section PackedLocator_LocatorBatchProductRoute
/-!
# Collision-free extraction from a batch of regular factors

Let `A` be a finite set of distinct regular factors and let `P` be their
product.  Suppose a shared power route has reached a quotient family `q` at
depth `j`, so an original row has the form `P^j * q v`.  At the first stage
where not every factor divides every value of `q`, the nonuniversal
divisibility conditions are proper submodules.  A finite-union argument
chooses one `v` avoiding all of them simultaneously.

For `F ∈ A` put `G_F = ∏ (A.erase F)` and retain the cofactor in the
helper:

`Q_F = G_F^j * q v`.

Then `P^j * q v = F^j * Q_F`.  Consequently the order-`j` derivative
extraction makes `Q_F` vanish on every `F`-regular seed, including seeds at
which another factor vanishes.  There is no internal-collision error term or
collision charge.  Pairwise coprimality also gives `IsRelPrime F Q_F`, and
the cofactor exactly restores all residual weight lost to the other factors.
-/

namespace ProximityPrize.SubmissionLower.LocatorBatchProductRoute

open scoped BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient
  LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
  LocatorTwoFactorAvoidance

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K V : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

abbrev P4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-! ## Divisibility subspaces and simultaneous avoidance -/

/-- The preimage under a linear polynomial family of the principal ideal
generated by `F`. -/
def dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) : Submodule K V where
  carrier := {v | F ∣ q v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change F ∣ q x at hx
    change F ∣ q y at hy
    change F ∣ q (x + y)
    rw [map_add]
    exact dvd_add hx hy
  smul_mem' := by
    intro a x hx
    change F ∣ q x at hx
    change F ∣ q (a • x)
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hx _

@[simp] theorem mem_dvdSubmodule [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K) (v : V) :
    v ∈ dvdSubmodule q F ↔ F ∣ q v := Iff.rfl

theorem dvdSubmodule_ne_top_of_not_universal
    [AddCommGroup V] [Module K V]
    (q : V →ₗ[K] P4 K) (F : P4 K)
    (h : ¬ ∀ v, F ∣ q v) :
    dvdSubmodule q F ≠ ⊤ := by
  intro htop
  apply h
  intro v
  have hv : v ∈ dvdSubmodule q F := by rw [htop]; trivial
  exact hv

/-- A field with more elements than the number of nonuniversal factors
contains one vector avoiding every corresponding divisibility subspace.
The vector is automatically nonzero when the factor set is nonempty. -/
theorem exists_avoiding_nonuniversal_factors
    [AddCommGroup V] [Module K V]
    {A : Type} [DecidableEq A] (s : Finset A) (hs : s.Nonempty)
    (q : V →ₗ[K] P4 K) (factor : A → P4 K)
    (hnonuniversal : ∀ a ∈ s, ¬ ∀ v, factor a ∣ q v)
    (hcard : s.card < ENat.card K) :
    ∃ v, v ≠ 0 ∧ ∀ a ∈ s, ¬ factor a ∣ q v := by
  classical
  let bad : s → Submodule K V := fun a => dvdSubmodule q (factor a.1)
  have hproper : ∀ a : s, bad a ≠ ⊤ := by
    intro a
    exact dvdSubmodule_ne_top_of_not_universal q (factor a.1)
      (hnonuniversal a.1 a.2)
  have hsmall : (Finset.univ : Finset s).card < ENat.card K := by
    simpa using hcard
  have hss := RCN133.finite_iUnion_ssubset
    (Finset.univ : Finset s) bad hproper hsmall
  obtain ⟨v, hv⟩ := Set.ssubset_univ_iff_nonempty_compl.mp hss
  have havoid : ∀ a : s, v ∉ bad a := by
    intro a hmem
    apply hv
    simp only [Set.mem_iUnion, Finset.mem_univ, true_and]
    exact ⟨a, trivial, hmem⟩
  have hv0 : v ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := hs
    have hnot := havoid ⟨a, ha⟩
    apply hnot
    subst v
    change factor a ∣ q 0
    simp
  refine ⟨v, hv0, ?_⟩
  intro a ha
  simpa only [bad, mem_dvdSubmodule] using havoid ⟨a, ha⟩

/-! ## Products of distinct regular factors -/

/-- The squarefree product represented by a finite set of regular indices. -/
def regularProduct (H : P4 K) (A : Finset (RCN266.RegularIndex H)) : P4 K :=
  ∏ F ∈ A, F.1

/-- The complementary product after removing one regular index. -/
def regularCofactor (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) : P4 K :=
  ∏ G ∈ A.erase F, G.1

theorem regularFactor_ne_zero (H : P4 K) (F : RCN266.RegularIndex H) :
    F.1 ≠ 0 :=
  (RCN167.positiveRFactors_spec H F.1 F.2).1.ne_zero

theorem regularProduct_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) : regularProduct H A ≠ 0 := by
  classical
  unfold regularProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  exact regularFactor_ne_zero H F

theorem regularCofactor_ne_zero (H : P4 K)
    (A : Finset (RCN266.RegularIndex H)) (F : RCN266.RegularIndex H) :
    regularCofactor H A F ≠ 0 := by
  classical
  unfold regularCofactor
  apply Finset.prod_ne_zero_iff.mpr
  intro G hG
  exact regularFactor_ne_zero H G

/-- Exact factor/cofactor decomposition of the batch product. -/
theorem regularFactor_mul_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    F.1 * regularCofactor H A F = regularProduct H A := by
  classical
  simpa only [regularProduct, regularCofactor] using
    Finset.mul_prod_erase A (fun G => G.1) hFA

/-- A regular factor is coprime to the product of all the other regular
factors in the same finite set. -/
theorem regularFactor_isRelPrime_cofactor
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A) :
    IsRelPrime F.1 (regularCofactor H A F) := by
  classical
  unfold regularCofactor
  apply IsRelPrime.prod_right
  intro G hG
  have hGe := Finset.mem_erase.mp hG
  apply regularIndex_isRelPrime_of_ne H F G
  intro heq
  apply hGe.1
  exact Subtype.ext heq.symm

/-- Splitting a batch power around one selected factor. -/
theorem regularProduct_power_split
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) :
    regularProduct H A ^ j * J =
      F.1 ^ j * (regularCofactor H A F ^ j * J) := by
  rw [← regularFactor_mul_cofactor H A F hFA, mul_pow]
  ring

/-- Avoiding `F` in the common residual witness makes the cofactor-retaining
helper coprime to `F`. -/
theorem regularFactor_isRelPrime_liftedHelper
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (j : ℕ) (J : P4 K) (hnot : ¬ F.1 ∣ J) :
    IsRelPrime F.1 (regularCofactor H A F ^ j * J) := by
  have hFirred := (RCN167.positiveRFactors_spec H F.1 F.2).1
  apply hFirred.isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hnot
  exact ((regularFactor_isRelPrime_cofactor H A F hFA).pow_right)
    |>.dvd_of_dvd_mul_left hd

/-! ## Exact restoration of residual weights -/

/-- Multiplying the common residual witness by the complementary product
restores precisely the weight spent on all factors other than `F`. -/
theorem cofactor_power_mul_weight_le_sub
    (weights : Fin 4 → ℕ) (B j : ℕ) (F C J : P4 K)
    (hF : F ≠ 0) (hC : C ≠ 0) (hJ : J ≠ 0)
    (hfeasible : j * wt weights (F * C) ≤ B)
    (hbound : wt weights J ≤ B - j * wt weights (F * C)) :
    wt weights (C ^ j * J) ≤ B - j * wt weights F := by
  have hFC := weightedTotalDegree_mul weights F C hF hC
  have hCJ := weightedTotalDegree_mul weights (C ^ j) J
    (pow_ne_zero j hC) hJ
  have hCp := wt_pow_eq weights C hC j
  unfold wt at hfeasible hbound hFC hCJ hCp ⊢
  rw [hFC, Nat.mul_add] at hfeasible hbound
  rw [hCp] at hCJ
  rw [hCJ]
  let f := MvPolynomial.weightedTotalDegree weights F
  let c := MvPolynomial.weightedTotalDegree weights C
  let x := MvPolynomial.weightedTotalDegree weights J
  change j * f + j * c ≤ B at hfeasible
  change x ≤ B - (j * f + j * c) at hbound
  change j * c + x ≤ B - j * f
  have htotal : j * f + (j * c + x) ≤ B := by
    calc
      j * f + (j * c + x) = (j * f + j * c) + x := by omega
      _ ≤ (j * f + j * c) + (B - (j * f + j * c)) :=
        Nat.add_le_add_left hbound _
      _ = B := Nat.add_sub_of_le hfeasible
  have htotal' : (j * c + x) + j * f ≤ B := by
    simpa only [Nat.add_comm] using htotal
  exact Nat.le_sub_of_add_le htotal'

/-- The three residual bounds for every lifted helper. -/
theorem liftedHelper_residual_bounds
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (F : RCN266.RegularIndex H) (hFA : F ∈ A)
    (T YS S j : ℕ) (J : P4 K) (hJ : J ≠ 0)
    (hT : wt residualTotalWeights J ≤
      T - j * wt residualTotalWeights (regularProduct H A))
    (hY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights (regularProduct H A))
    (hS : wt residualSWeights J ≤
      S - j * wt residualSWeights (regularProduct H A))
    (hTfeasible : j * wt residualTotalWeights (regularProduct H A) ≤ T)
    (hYfeasible : j * wt residualYSWeights (regularProduct H A) ≤ YS)
    (hSfeasible : j * wt residualSWeights (regularProduct H A) ≤ S) :
    wt residualTotalWeights (regularCofactor H A F ^ j * J) ≤
        T - j * wt residualTotalWeights F.1 ∧
      wt residualYSWeights (regularCofactor H A F ^ j * J) ≤
        YS - j * wt residualYSWeights F.1 ∧
      wt residualSWeights (regularCofactor H A F ^ j * J) ≤
        S - j * wt residualSWeights F.1 := by
  have hfactor := regularFactor_mul_cofactor H A F hFA
  have hF0 := regularFactor_ne_zero H F
  have hC0 := regularCofactor_ne_zero H A F
  rw [← hfactor] at hT hY hS hTfeasible hYfeasible hSfeasible
  exact ⟨
    cofactor_power_mul_weight_le_sub residualTotalWeights T j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hTfeasible hT,
    cofactor_power_mul_weight_le_sub residualYSWeights YS j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hYfeasible hY,
    cofactor_power_mul_weight_le_sub residualSWeights S j F.1
      (regularCofactor H A F) J hF0 hC0 hJ hSfeasible hS⟩

/-! ## One common witness and all collision-free helpers -/

/-- At a nonuniversal batch stage, one vector gives coprime helpers for every
nonuniversal factor, with the sharp per-factor residual caps.

Crucially, `hnonuniversal` concerns the displayed current family `q`.  It must
be established again after every high-band projection; nonuniversality on an
earlier ambient family does not survive restriction to a kernel. -/
theorem exists_collisionFree_batch_helpers
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A N : Finset (RCN266.RegularIndex H))
    (hNA : N ⊆ A) (hN : N.Nonempty)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (j Dq w T YS S : ℕ)
    (hbox : ∀ v, q v ∈ nestedCoefficientBox K Dq w
      (T - j * wt residualTotalWeights (regularProduct H A))
      (YS - j * wt residualYSWeights (regularProduct H A))
      (S - j * wt residualSWeights (regularProduct H A)))
    (hfeasible :
      j * wt residualTotalWeights (regularProduct H A) ≤ T ∧
      j * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      j * wt residualSWeights (regularProduct H A) ≤ S)
    (hnonuniversal : ∀ F ∈ N, ¬ ∀ v, F.1 ∣ q v)
    (hcard : N.card < ENat.card K) :
    ∃ (v : V) (J : P4 K),
      v ≠ 0 ∧ J = q v ∧ J ≠ 0 ∧
      ∀ F ∈ N,
        let QF := regularCofactor H A F ^ j * J
        QF ≠ 0 ∧ IsRelPrime F.1 QF ∧
          regularProduct H A ^ j * J = F.1 ^ j * QF ∧
          wt residualTotalWeights QF ≤
            T - j * wt residualTotalWeights F.1 ∧
          wt residualYSWeights QF ≤
            YS - j * wt residualYSWeights F.1 ∧
          wt residualSWeights QF ≤
            S - j * wt residualSWeights F.1 := by
  classical
  obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
    N hN q (fun F => F.1) hnonuniversal hcard
  let J := q v
  have hJ : J ≠ 0 := by
    intro hz
    apply hv
    apply hq
    simpa only [J, map_zero] using hz
  have hweights := nested_mem_weights (hbox v) hJ
  refine ⟨v, J, hv, rfl, hJ, ?_⟩
  intro F hFN
  have hFA := hNA hFN
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 :=
    mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFN)
  have heq := regularProduct_power_split H A F hFA j J
  have hb := liftedHelper_residual_bounds H A F hFA T YS S j J hJ
    hweights.1 hweights.2.1 hweights.2.2.1
    hfeasible.1 hfeasible.2.1 hfeasible.2.2
  exact ⟨hQF, hrel, heq, hb⟩

/-! ## The current post-projection split -/

/-- Factors whose divisibility subspace is the whole *current* domain. -/
noncomputable def universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Finset (RCN266.RegularIndex H) := by
  classical
  exact A.filter fun F => ∀ v, F.1 ∣ q v

@[simp] theorem mem_universalFactors
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (F : RCN266.RegularIndex H) :
    F ∈ universalFactors H A q ↔ F ∈ A ∧ ∀ v, F.1 ∣ q v := by
  classical
  simp only [universalFactors, Finset.mem_filter]

theorem universalFactors_subset
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : universalFactors H A q ⊆ A := by
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.1

/-- Individual universal divisibility combines to divisibility by the entire
squarefree regular product. -/
theorem regularProduct_dvd_of_each
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (Q : P4 K)
    (hdiv : ∀ F ∈ A, F.1 ∣ Q) : regularProduct H A ∣ Q := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [regularProduct, Finset.notMem_empty,
      Finset.prod_empty, one_dvd]
  | @insert F A hFA ih =>
      have hFdiv : F.1 ∣ Q := hdiv F (Finset.mem_insert_self F A)
      have hAdiv : regularProduct H A ∣ Q := by
        apply ih
        intro G hGA
        exact hdiv G (Finset.mem_insert_of_mem hGA)
      have hrel : IsRelPrime F.1 (regularProduct H A) := by
        unfold regularProduct
        apply IsRelPrime.prod_right
        intro G hGA
        apply regularIndex_isRelPrime_of_ne H F G
        intro heq
        apply hFA
        have hFG : F = G := Subtype.ext heq
        rwa [hFG]
      have hprod : regularProduct H (insert F A) =
          F.1 * regularProduct H A := by
        simp only [regularProduct, Finset.prod_insert hFA]
      rw [hprod]
      exact hrel.mul_dvd hFdiv hAdiv

/-- The squarefree product of any set of regular indices divides the
ambient carrier polynomial.  This is the bridge used after a universal
source split: the source controls the product's narrow coordinates, while
the selected carrier still controls its total coordinate. -/
theorem regularProduct_dvd_carrier
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) :
    regularProduct H A ∣ H := by
  apply regularProduct_dvd_of_each
  intro F _hFA
  exact (RCN167.positiveRFactors_spec H F.1 F.2).2.1

/-- The product of the current universal subset divides every value of the
current family. -/
theorem universalProduct_dvd
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) :
    ∀ v, regularProduct H (universalFactors H A q) ∣ q v := by
  intro v
  apply regularProduct_dvd_of_each
  intro F hF
  exact (mem_universalFactors H A q F).mp hF |>.2 v

/-- Packaged conclusion of `exists_collisionFree_batch_helpers`. -/
def HasCollisionFreeBatchHelpers
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A N : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (j T YS S : ℕ) : Prop :=
  ∃ (v : V) (J : P4 K),
    v ≠ 0 ∧ J = q v ∧ J ≠ 0 ∧
    ∀ F ∈ N,
      let QF := regularCofactor H A F ^ j * J
      QF ≠ 0 ∧ IsRelPrime F.1 QF ∧
        regularProduct H A ^ j * J = F.1 ^ j * QF ∧
        wt residualTotalWeights QF ≤
          T - j * wt residualTotalWeights F.1 ∧
        wt residualYSWeights QF ≤
          YS - j * wt residualYSWeights F.1 ∧
        wt residualSWeights QF ≤
          S - j * wt residualSWeights F.1

/-- One explicit adapter from a current post-projection family to the U/N
case split used by the abstract phase recursion.

If every factor is universal, the first component supplies divisibility by
the whole product for the next shared quotient round.  Otherwise `U` is a
strict subset and one common witness supplies all helpers for `N = A \ U`.
The recursive child on `U` should normally be built from a fresh source; this
theorem intentionally does not claim that restricting or quotienting the
current family preserves nonuniversality. -/
theorem currentPostProjection_split
    [AddCommGroup V] [Module K V]
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (j Dq w T YS S : ℕ)
    (hbox : ∀ v, q v ∈ nestedCoefficientBox K Dq w
      (T - j * wt residualTotalWeights (regularProduct H A))
      (YS - j * wt residualYSWeights (regularProduct H A))
      (S - j * wt residualSWeights (regularProduct H A)))
    (hfeasible :
      j * wt residualTotalWeights (regularProduct H A) ≤ T ∧
      j * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      j * wt residualSWeights (regularProduct H A) ≤ S)
    (hfield : ∀ B : Finset (RCN266.RegularIndex H), B ⊆ A →
      B.card < ENat.card K) :
    let U := universalFactors H A q
    (∀ v, regularProduct H U ∣ q v) ∧
      (U = A ∨
        U ⊂ A ∧ HasCollisionFreeBatchHelpers H A (A \ U) q j T YS S) := by
  classical
  let U := universalFactors H A q
  have hUsub : U ⊆ A := universalFactors_subset H A q
  have hprod : ∀ v, regularProduct H U ∣ q v :=
    universalProduct_dvd H A q
  refine ⟨hprod, ?_⟩
  by_cases hall : U = A
  · exact Or.inl hall
  · right
    have hproper : U ⊂ A :=
      (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
    have hN : (A \ U).Nonempty := by
      apply Finset.sdiff_nonempty.mpr
      intro hAU
      exact hall (Finset.Subset.antisymm hUsub hAU)
    have hnonuniversal : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ q v := by
      intro F hFN hdiv
      have hparts := Finset.mem_sdiff.mp hFN
      apply hparts.2
      exact (mem_universalFactors H A q F).mpr ⟨hparts.1, hdiv⟩
    refine ⟨hproper, ?_⟩
    exact exists_collisionFree_batch_helpers H A (A \ U)
      Finset.sdiff_subset hN q hq j Dq w T YS S hbox hfeasible
      hnonuniversal (hfield (A \ U) Finset.sdiff_subset)

/-! ## Quotienting a fully universal batch -/

private theorem sub_mul_then_one (a b j:ℕ):
    a-j*b-b=a-(j+1)*b:=by
  rw [Nat.sub_sub,Nat.add_mul,one_mul]

/-- A raw constraint-kernel reconstruction lies in the nested source box as
soon as the usual contact/slope shape inequality supplies its YS cap. -/
theorem kernelReconstruct_mem_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1)):
    ∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      kernelReconstructLinear (K:=K) D w L S m nodes u0 u1 v ∈
        nestedCoefficientBox K D w L YS S:=by
  intro v d hd
  have hglobal:=reconstruct_mem_globalCoefficientBox K D w L S v.1
  have hb:=hglobal hd
  have hYS:=flag_box_ys_bound D w L S YS hw hshape
    (reconstruct K D w L S v.1) hglobal
  have hy:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hYS
  rw [weight_fin4] at hy
  simp only [residualYSWeights] at hy
  refine ⟨hb.1,?_,hb.2.1,hb.2.2⟩
  simpa [residualYSWeights] using hy

/-- Source-entry adapter for a universally divisible squarefree regular
product.  This is the batch analogue of the single-factor private
`quotient_nested` construction: it builds the injective quotient family and
subtracts the product's four weights exactly once. -/
theorem kernelQuotient_regularProduct_nested
    {I:Type} [Fintype I]
    (D w L S m YS:ℕ) (nodes u0 u1:I → K)
    (hw:1 ≤ w) (hshape:D+S ≤ w*(YS+1))
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L S m nodes u0 u1,
      regularProduct H A ∣ reconstruct K D w L S v.1):
    ∃ q:ConstraintKernel (K:=K) D w L S m nodes u0 u1 →ₗ[K] P4 K,
      Function.Injective q ∧
      (∀ v,reconstruct K D w L S v.1=regularProduct H A*q v) ∧
      ∀ v,q v ∈ nestedCoefficientBox K
        (D-wt (contactWeights w) (regularProduct H A)) w
        (L-wt residualTotalWeights (regularProduct H A))
        (YS-wt residualYSWeights (regularProduct H A))
        (S-wt residualSWeights (regularProduct H A)):=by
  let recon:=kernelReconstructLinear (K:=K) D w L S m nodes u0 u1
  have hdiv':∀ v,regularProduct H A ∣ recon v:=by
    intro v
    simpa only [recon,kernelReconstructLinear_apply] using hdiv v
  obtain ⟨hq,hprod,hbox⟩:=quotientLinear_nested_data D w L YS S recon
    (kernelReconstructLinear_injective (K:=K) D w L S m nodes u0 u1)
    (kernelReconstruct_mem_nested D w L S m YS nodes u0 u1 hw hshape)
    (regularProduct H A) (regularProduct_ne_zero H A) hdiv'
  let q:=quotientLinear recon (regularProduct H A)
    (regularProduct_ne_zero H A) hdiv'
  refine ⟨q,hq,?_,?_⟩
  · intro v
    simpa only [recon,kernelReconstructLinear_apply,q] using hprod v
  · exact hbox

/-- If the entire current batch product divides an injective family, divide
by that product in one operation.  The family remains injective, the product
power advances from `j` to `j+1`, and all four residual coordinates are
normalized to the new exponent. -/
theorem quotient_by_universal_regularProduct
    [AddCommGroup V] [Module K V]
    (H:P4 K) (A:Finset (RCN266.RegularIndex H))
    (q:V →ₗ[K] P4 K) (hq:Function.Injective q)
    (j Dq w T YS S:ℕ)
    (hmem:∀ v,q v ∈ nestedCoefficientBox K Dq w
      (T-j*wt residualTotalWeights (regularProduct H A))
      (YS-j*wt residualYSWeights (regularProduct H A))
      (S-j*wt residualSWeights (regularProduct H A)))
    (hdiv:∀ v,regularProduct H A ∣ q v):
    ∃ qNext:V →ₗ[K] P4 K,
      Function.Injective qNext ∧
      (∀ v,regularProduct H A^j*q v=
        regularProduct H A^(j+1)*qNext v) ∧
      ∀ v,qNext v ∈ nestedCoefficientBox K
        (Dq-wt (contactWeights w) (regularProduct H A)) w
        (T-(j+1)*wt residualTotalWeights (regularProduct H A))
        (YS-(j+1)*wt residualYSWeights (regularProduct H A))
        (S-(j+1)*wt residualSWeights (regularProduct H A)):=by
  classical
  let P:=regularProduct H A
  let qNext:=quotientLinear q P (regularProduct_ne_zero H A) hdiv
  obtain ⟨hqNext,hprod,hnext⟩:=quotientLinear_nested_data
    Dq w
      (T-j*wt residualTotalWeights P)
      (YS-j*wt residualYSWeights P)
      (S-j*wt residualSWeights P)
      q hq hmem P (regularProduct_ne_zero H A) hdiv
  refine ⟨qNext,hqNext,?_,?_⟩
  · intro v
    change P^j*q v=P^(j+1)*qNext v
    rw [hprod v,pow_succ]
    ring
  · intro v
    have hv:=hnext v
    simpa only [P,sub_mul_then_one] using hv


/-! ## First strict exit in a shared product-power chain -/

/-- A shared band chain exits when the post-projection universal factors form
a strict subset `U` of the current batch.  The index `j` counts additional
whole-product quotients after the displayed input family `q`; thus a source
which was quotiented once before calling this interface has original power
`j+1` at the exit. -/
def HasBatchExitStage
    [AddCommGroup V] [Module K V]
    (fuel Dlow w delta T YS S : ℕ)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (q : V →ₗ[K] P4 K) : Prop :=
  ∃ (j : Fin fuel) (U : Finset (RCN266.RegularIndex H)) (v : V) (J : P4 K),
    U ⊂ A ∧ v ≠ 0 ∧ J ≠ 0 ∧
      regularProduct H A ^ j.val * J = q v ∧
      J ∈ nestedCoefficientBox K
        (Dlow - j.val * delta -
          j.val * wt (contactWeights w) (regularProduct H A)) w
        (T - j.val * wt residualTotalWeights (regularProduct H A))
        (YS - j.val * wt residualYSWeights (regularProduct H A))
        (S - j.val * wt residualSWeights (regularProduct H A)) ∧
      ∀ F ∈ A \ U, ¬ F.1 ∣ J

/-- The batch analogue of `exists_power_stage_of_bandBudget_succ`.  At each
band the universal subset is recomputed on the projected family.  A proper
subset exits immediately; an all-universal stage quotients the entire
squarefree product and continues.  The terminal residual inequality rules
out an all-universal final stage.

This theorem is deliberately only the linear-algebraic stage selector.  Its
consumer multiplies the retained cofactor back into `J`, performs derivative
extraction, and applies the desired helper-count cap. -/
theorem exists_batchExitStage_of_bandBudget_succ
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (steps Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] P4 K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (hA : A.Nonempty)
    (hsource :
      powerBandBudget delta
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          T YS S (steps + 1) < Module.finrank K V)
    (hterminal :
      T - steps * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - steps * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - steps * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfield : A.card < ENat.card K) :
    HasBatchExitStage (steps + 1) Dlow w delta T YS S H A q := by
  classical
  let P := regularProduct H A
  have hP : P ≠ 0 := by
    simpa only [P] using regularProduct_ne_zero H A
  change powerBandBudget delta
      (wt residualTotalWeights P) (wt residualYSWeights P)
      (wt residualSWeights P) T YS S (steps + 1) <
    Module.finrank K V at hsource
  change
    T - steps * wt residualTotalWeights P < wt residualTotalWeights P ∨
    YS - steps * wt residualYSWeights P < wt residualYSWeights P ∨
    S - steps * wt residualSWeights P < wt residualSWeights P at hterminal
  induction steps generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hfirst : delta * channelCount T YS S < Module.finrank K V := by
          simpa only [powerBandBudget, Nat.add_zero] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        exfalso
        obtain ⟨v, hv⟩ :=
          Module.finrank_pos_iff_exists_ne_zero.mp hlowOneRank
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        have hb := nested_mem_weights (hqOneBox v) hqv
        have hdivT : wt residualTotalWeights P ≤
            wt residualTotalWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualTotalWeights P
              (qOne v) (hdivP v) hqv
        have hdivY : wt residualYSWeights P ≤
            wt residualYSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualYSWeights P
              (qOne v) (hdivP v) hqv
        have hdivS : wt residualSWeights P ≤
            wt residualSWeights (qOne v) := by
          simpa only [wt] using
            weightedTotalDegree_le_of_dvd residualSWeights P
              (qOne v) (hdivP v) hqv
        rcases hterminal with ht | hy | hs
        · apply (not_lt_of_ge (hdivT.trans hb.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using ht
        · apply (not_lt_of_ge (hdivY.trans hb.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hy
        · apply (not_lt_of_ge (hdivS.trans hb.2.2.1))
          simpa only [Nat.zero_mul, Nat.sub_zero] using hs
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
  | succ steps ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          powerBandBudget delta
              (wt residualTotalWeights P) (wt residualYSWeights P)
              (wt residualSWeights P)
              (T - wt residualTotalWeights P)
              (YS - wt residualYSWeights P)
              (S - wt residualSWeights P) (steps + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        have hbudget :
            delta * channelCount T YS S +
                powerBandBudget delta
                  (wt residualTotalWeights P) (wt residualYSWeights P)
                  (wt residualSWeights P)
                  (T - wt residualTotalWeights P)
                  (YS - wt residualYSWeights P)
                  (S - wt residualSWeights P) (steps + 1) <
              Module.finrank K V := by
          simpa only [powerBandBudget, Nat.succ_eq_add_one,
            Nat.add_assoc] using hsource
        omega
      let qOne : lowOne →ₗ[K] P4 K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      let U := universalFactors H A qOne
      have hUsub : U ⊆ A := universalFactors_subset H A qOne
      by_cases hall : U = A
      · have hdivP : ∀ v : lowOne, P ∣ qOne v := by
          intro v
          have hv := universalProduct_dvd H A qOne v
          change regularProduct H U ∣ qOne v at hv
          rw [hall] at hv
          simpa only [P] using hv
        let qTwo := quotientLinear qOne P hP hdivP
        obtain ⟨hqTwo, _hprodTwo, hqTwoBox⟩ :=
          quotientLinear_nested_data Dlow w T YS S qOne hqOne hqOneBox
            P hP hdivP
        let DOneHigh := Dlow - wt (contactWeights w) P
        let DOneLow := Dlow - delta - wt (contactWeights w) P
        let TOne := T - wt residualTotalWeights P
        let YOne := YS - wt residualYSWeights P
        let SOne := S - wt residualSWeights P
        have hwidthRest : DOneHigh ≤ DOneLow + delta := by
          simp only [DOneHigh, DOneLow]
          omega
        have hterminalRest :
            TOne - steps * wt residualTotalWeights P <
                wt residualTotalWeights P ∨
            YOne - steps * wt residualYSWeights P <
                wt residualYSWeights P ∨
            SOne - steps * wt residualSWeights P <
                wt residualSWeights P := by
          rcases hterminal with ht | hy | hs
          · left
            simpa only [TOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using ht
          · right; left
            simpa only [YOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hy
          · right; right
            simpa only [SOne, Nat.sub_sub, Nat.add_mul, one_mul,
              Nat.succ_eq_add_one, Nat.add_comm] using hs
        obtain ⟨j, child, v, J, hchild, hv, hJ, heq, hbox, havoid⟩ :=
          ih DOneHigh DOneLow TOne YOne SOne hwidthRest qTwo hqTwo
            (by simpa only [qTwo, DOneHigh, TOne, YOne, SOne] using hqTwoBox)
            (by simpa only [TOne, YOne, SOne] using hlowOneRank)
            hterminalRest
        let jUp : Fin (Nat.succ steps + 1) := ⟨j.val + 1, by omega⟩
        refine ⟨jUp, child, v.1, J, hchild, ?_, hJ, ?_, ?_, havoid⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · change P ^ (j.val + 1) * J = q v.1
          calc
            P ^ (j.val + 1) * J = P * (P ^ j.val * J) := by
              rw [pow_succ']
              ring
            _ = P * qTwo v := by rw [heq]
            _ = qOne v :=
              (recon_eq_mul_quotientPolynomial qOne P hdivP v).symm
            _ = q v.1 := rfl
        · have hD :
              DOneLow - j.val * delta -
                  j.val * wt (contactWeights w) P =
                Dlow - (j.val + 1) * delta -
                  (j.val + 1) * wt (contactWeights w) P := by
              simp only [DOneLow, Nat.sub_sub, Nat.add_mul, one_mul]
              congr 1
              omega
          have hT : TOne - j.val * wt residualTotalWeights P =
              T - (j.val + 1) * wt residualTotalWeights P := by
            simp only [TOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hY : YOne - j.val * wt residualYSWeights P =
              YS - (j.val + 1) * wt residualYSWeights P := by
            simp only [YOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          have hS : SOne - j.val * wt residualSWeights P =
              S - (j.val + 1) * wt residualSWeights P := by
            simp only [SOne, Nat.sub_sub, Nat.add_mul, one_mul]
            congr 1
            omega
          change J ∈ nestedCoefficientBox K
            (DOneLow - j.val * delta -
              j.val * wt (contactWeights w) P) w
            (TOne - j.val * wt residualTotalWeights P)
            (YOne - j.val * wt residualYSWeights P)
            (SOne - j.val * wt residualSWeights P) at hbox
          change J ∈ nestedCoefficientBox K
            (Dlow - (j.val + 1) * delta -
              (j.val + 1) * wt (contactWeights w) P) w
            (T - (j.val + 1) * wt residualTotalWeights P)
            (YS - (j.val + 1) * wt residualYSWeights P)
            (S - (j.val + 1) * wt residualSWeights P)
          rw [hD, hT, hY, hS] at hbox
          exact hbox
      · have hproper : U ⊂ A :=
          (_root_.ssubset_iff_subset_ne).mpr ⟨hUsub, hall⟩
        have hN : (A \ U).Nonempty := by
          apply Finset.sdiff_nonempty.mpr
          intro hAU
          exact hall (Finset.Subset.antisymm hUsub hAU)
        have hnon : ∀ F ∈ A \ U, ¬ ∀ v, F.1 ∣ qOne v := by
          intro F hFN hdiv
          have hp := Finset.mem_sdiff.mp hFN
          apply hp.2
          exact (mem_universalFactors H A qOne F).mpr ⟨hp.1, hdiv⟩
        have hNcard : (A \ U).card < ENat.card K := by
          calc
            ((A \ U).card : ENat) ≤ (A.card : ENat) := by
              exact_mod_cast (Finset.card_le_card Finset.sdiff_subset)
            _ < ENat.card K := hfield
        obtain ⟨v, hv, havoid⟩ := exists_avoiding_nonuniversal_factors
          (A \ U) hN qOne (fun F => F.1) hnon hNcard
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hqOne
          simpa only [map_zero] using hz
        refine ⟨⟨0, by omega⟩, U, v.1, qOne v, hproper, ?_, hqv, ?_, ?_, ?_⟩
        · intro hz
          apply hv
          exact Subtype.ext hz
        · simp only [Fin.val_zero, pow_zero, one_mul, qOne,
            LinearMap.comp_apply, Submodule.coe_subtype]
        · simpa only [Fin.val_zero, zero_mul, Nat.sub_zero] using hqOneBox v
        · exact havoid
end
end ProximityPrize.SubmissionLower.LocatorBatchProductRoute
end PackedLocator_LocatorBatchProductRoute
end Compact_PackedLocatorTail
