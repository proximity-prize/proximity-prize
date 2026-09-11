import ProximityPrize.SubmissionLower.PartG001_03
section Compact_PackedLocatorTail
section PackedLocator_LocatorPhase6800Oracle
namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch
set_option autoImplicit false
set_option maxRecDepth 100000


def sumFlag {ι : Type} (s : Finset ι) (p : ι → FlagDegree) : FlagDegree :=
  ⟨∑ i ∈ s, (p i).zOnly, ∑ i ∈ s, (p i).yz,
    ∑ i ∈ s, (p i).all⟩

@[simp] theorem sumFlag_all {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    (sumFlag s p).all = ∑ i ∈ s, (p i).all := rfl

@[simp] theorem sumFlag_middle {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    middle (sumFlag s p) = ∑ i ∈ s, middle (p i) := by
  simp only [sumFlag, middle, Finset.sum_add_distrib]

@[simp] theorem sumFlag_total {ι : Type} (s : Finset ι)
    (p : ι → FlagDegree) :
    total (sumFlag s p) = ∑ i ∈ s, total (p i) := by
  simp only [sumFlag, total, Finset.sum_add_distrib]

theorem sum_initialAPotential_eval {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → FlagDegree) :
    (∑ i ∈ s, initialAPotential.eval (p i)) =
      initialAPotential.eval (sumFlag s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Aggregate direct-A helper ledger for the factors that leave the initial
split.  The exact greedy complement avoids the seven-trillion loss of three
independent cumulative-coordinate remainders. -/
theorem initialA_helpers_sum_le_complementCore
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 6677)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 153)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 33) :
    (∑ i ∈ s, helper i) ≤ initialAComplementCore universal := by
  calc
    (∑ i ∈ s, helper i) ≤ ∑ i ∈ s, initialAPotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi => hhelper i hi)
    _ = initialAPotential.eval (sumFlag s p) := sum_initialAPotential_eval s p
    _ ≤ initialAComplementCore universal := by
      apply initialAPotential_le_complementCore
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr

theorem initialA_helpers_sum_le_complement
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 6677)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 153)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 33) :
    (∑ i ∈ s, helper i) ≤ initialAComplement universal :=
  (initialA_helpers_sum_le_complementCore s p helper universal hhelper ht hy hr).trans
    (initialAComplementCore_le universal)

/-- A threshold row says at which `z` each source becomes routeable for fixed
positive slope `r` and residual middle coordinate `v`. -/
structure ThresholdReceipt where
  r : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : ℕ
  split500 : ℕ
  split1200 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def thresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  let maxZ := 6677 - (r + v)
  if threshold = 0 then s.Routeable (rawFlag r v 0)
  else if threshold ≤ maxZ then
    ¬s.Routeable (rawFlag r v (threshold - 1)) ∧
      s.Routeable (rawFlag r v threshold)
  else threshold = maxZ + 1 ∧ ¬s.Routeable (rawFlag r v maxZ)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (thresholdBoundary s r v threshold) := by
  unfold thresholdBoundary
  infer_instance

def ThresholdReceipt.Valid (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    thresholdBoundary sourceR1200 q.r q.v q.r1200 ∧
    thresholdBoundary LocatorPhase6800Oracle.sourceC q.r q.v q.sourceC ∧
    thresholdBoundary sourceSplit500 q.r q.v q.split500 ∧
    thresholdBoundary sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable q.Valid := by
  unfold ThresholdReceipt.Valid
  infer_instance

/-- A prefix row is the defect prefix after completing slope layer `afterR`.
`sourceC` has either 22 bucket entries (on the critical rectangle) or one
fully-z-forgotten entry. -/
structure PrefixReceipt where
  afterR : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : List ℕ
  split500 : ℕ
  split1200 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def PrefixReceipt.ExpectedShape (q : PrefixReceipt) : Prop :=
  1 ≤ q.afterR ∧ q.afterR ≤ 28 ∧ q.afterR + 1 + q.v ≤ 135 ∧
    q.sourceC.length = (if q.afterR ≤ 0 ∧ q.v ≤ 64 then 23 else 1)

instance (q : PrefixReceipt) : Decidable q.ExpectedShape := by
  unfold PrefixReceipt.ExpectedShape
  infer_instance

/-! ## Compact exact base table

For fixed raw `(r,v)`, the ordinary partition maximum is stored explicitly at
`z=0,1,2`.  From `z=3` onward it is the maximum of affine carrier lines.  A
segment stores its value at its first integer, avoiding signed intercepts.
-/

structure BaseSegment where
  start : ℕ
  valueAtStart : ℕ
  slope : ℕ
  deriving DecidableEq, Repr

def BaseSegment.evalAt (q : BaseSegment) (z : ℕ) : ℕ :=
  q.valueAtStart + q.slope * (z - q.start)

structure BaseRow where
  r : ℕ
  v : ℕ
  z0 : ℕ
  z1 : ℕ
  z2 : ℕ
  segments : List BaseSegment
  deriving DecidableEq, Repr

def evalBaseSegments : List BaseSegment → ℕ → ℕ
  | [], _ => 0
  | q :: qs, z =>
      (qs.foldl (fun best next => if next.start ≤ z then next else best) q).evalAt z

def BaseRow.evalAt (q : BaseRow) (z : ℕ) : ℕ :=
  if z = 0 then q.z0
  else if z = 1 then q.z1
  else if z = 2 then q.z2
  else evalBaseSegments q.segments z

/-- Row order used by the generated array: increasing `r`, then increasing
`v`, over `1 ≤ r ≤ 29` and `r+v ≤ 135`. -/
def baseRowIndex (r v : ℕ) : ℕ :=
  (r - 1) * 136 - ((r - 1) * r) / 2 + v

def defaultBaseRow : BaseRow := ⟨0, 0, 0, 0, 0, []⟩

def lookupBaseRow (rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  (rows[baseRowIndex r v]?).getD defaultBaseRow

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def BaseRowsIndexed (rows : Array BaseRow) : Prop :=
  rows.size = 3509 ∧
    ∀ r ∈ (List.range 29).map (fun q => q + 1),
      ∀ v ∈ List.range (136 - r),
        let q := lookupBaseRow rows r v
        q.r = r ∧ q.v = v

instance (rows : Array BaseRow) : Decidable (BaseRowsIndexed rows) := by
  unfold BaseRowsIndexed
  infer_instance

def BaseRow.ExpectedShape (q : BaseRow) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 135 ∧
    q.segments ≠ [] ∧ q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start) ∧
    ∀ s ∈ q.segments, s.start ≤ 6677 - (q.r + q.v)

instance (q : BaseRow) : Decidable q.ExpectedShape := by
  unfold BaseRow.ExpectedShape
  infer_instance

/-- State-local form of the base certificate.  Unlike the legacy full-box
interface below, this preserves the aggregate flag needed by every phase
transition. -/
def StateLocalBaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree),
    (∀ i ∈ s, 1 ≤ (p i).all) →
    (sumFlag s p).all ≤ 29 → middle (sumFlag s p) ≤ 135 →
    total (sumFlag s p) ≤ 6677 →
    (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap (sumFlag s p)

/-- Componentwise raw containment used by the defect-prefix recurrence. -/
def RawBelow (q p : FlagDegree) : Prop :=
  q.all ≤ p.all ∧ q.yz ≤ p.yz ∧ q.zOnly ≤ p.zOnly

def RawStrictSlopeBelow (q p : FlagDegree) : Prop :=
  RawBelow q p ∧ q.all < p.all

/-- Semantic condition checked by one phase's prefix table.  At a routeable
parent, every strict nonrouteable stopping child is paid by the stored defect.
The algebraic batch engine turns precisely this condition into the phase cap.
-/
def PhaseDefectSound (previousCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p q, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric recurrence represented by a checked phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p

/-- Abstract base certificate.  This isolates the discrete-convexity and the
two-coordinate unbounded knapsack proof from the algebraic phase consumer. -/
def BaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (p : ι → FlagDegree),
    (∀ i, 1 ≤ (p i).all) →
    (∑ i, (p i).all) ≤ 29 →
    (∑ i, middle (p i)) ≤ 135 →
    (∑ i, total (p i)) ≤ 6677 →
    (∑ i, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap ⟨6677 - 135, 135 - 30, 30⟩

/-- Consumer-facing abstraction: numerical receipt checking yields a narrow
phase cap, while the algebraic batch route supplies the phase transitions. -/
structure CheckedPhaseOracle where
  narrowCap : FlagDegree → ℕ
  baseCap : FlagDegree → ℕ
  baseSound : BaseOracleSound baseCap
  narrow_le : ∀ p, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    narrowCap p ≤ 269089533458270975
  joint_le : ∀ p, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6677 →
    narrowCap p + initialAComplement p ≤ 273301903386687639

/-! ## Generic finite-set transition consumed by the batch route -/


def certifiedNarrowMaximum : ℕ := 269089533458270975
/-- The 6802 regular allowance `254595720129422441` plus the fixed derivative chain
`ChainGroupMaj.chainMaj 33 153 = 3516784745477411`, which is now charged inside the
correlated complement instead of as a flat ledger term. -/
def certifiedJointMaximum : ℕ := 273301903386687639
def tightenedRegularAllowance : ℕ := 273301903386687639


end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex. -/
section PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex

open RCN095 LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def rawCost (r v z : ℕ) : ℕ := ordinaryCostOf ⟨z, v, r⟩

theorem hybridApplies_raw (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    HybridAppliesC2 (⟨z, v, r⟩ : FlagDegree) := by
  change 3 ≤ r ∧ r + 2 ≤ v + r
  omega

theorem padS_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) :
    padS (⟨z, v, r⟩ : FlagDegree) = r := by
  simp only [padS]
  omega

theorem padY_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
  simp only [padY, middle, padS_raw_hybrid r v z hr]
  omega

theorem padT_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
  simp only [padT, total, padY_raw_hybrid r v z hr hv]
  omega


theorem reduced_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    reducedTail (⟨z, v, r⟩ : FlagDegree) =
      ⟨2 * z * 131072, 1 + 2 * v * 131072, 2 * (r - 1) * 131072⟩ := by
  unfold reducedTail paddedTail
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem rational_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    rationalFlag (⟨z, v, r⟩ : FlagDegree) =
      ⟨131074 * z, 131074 * (v - 1) + 2, 131074 * (r - 2) + 3⟩ := by
  unfold rationalFlag
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem moving_raw_hybrid (r v z : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    movingFiber (⟨z, v, r⟩ : FlagDegree) = ⟨z, v, r + 1⟩ := by
  unfold movingFiber
  rw [padS_raw_hybrid r v z hr, padY_raw_hybrid r v z hr hv,
    padT_raw_hybrid r v z hr hv]
  congr <;> omega

theorem hybridCostC2_raw_affine (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * hybridCostC2 (⟨z + 1, v, r⟩ : FlagDegree) =
      hybridCostC2 ⟨z, v, r⟩ + hybridCostC2 ⟨z + 2, v, r⟩ := by
  have hr2 : 2 ≤ r := by omega
  unfold hybridCostC2 hybridCoordinateC1 movingCut
  rw [reduced_raw_hybrid r v z hr2 hv,
    reduced_raw_hybrid r v (z + 1) hr2 hv,
    reduced_raw_hybrid r v (z + 2) hr2 hv,
    rational_raw_hybrid r v z hr2 hv,
    rational_raw_hybrid r v (z + 1) hr2 hv,
    rational_raw_hybrid r v (z + 2) hr2 hv,
    moving_raw_hybrid r v z hr2 hv,
    moving_raw_hybrid r v (z + 1) hr2 hv,
    moving_raw_hybrid r v (z + 2) hr2 hv]
  unfold flagMixed
  simp only [add_zOnly, add_yz, add_all]
  ring

theorem rawCost_affine_of_hybrid (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  rw [rawCost, rawCost, rawCost]
  simp only [ordinaryCostOf, if_pos (hybridApplies_raw r v z hr hv),
    if_pos (hybridApplies_raw r v (z + 1) hr hv),
    if_pos (hybridApplies_raw r v (z + 2) hr hv)]
  exact hybridCostC2_raw_affine r v z hr hv

theorem paddedTail_raw_of_r_two_v_pos (r v z d : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    paddedTail (⟨z, v, r⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * v * d, 2 * (r - 1) * d⟩ := by
  unfold paddedTail
  have hs : padS (⟨z, v, r⟩ : FlagDegree) = r := by
    simp only [padS]
    omega
  have hy : padY (⟨z, v, r⟩ : FlagDegree) = r + v := by
    simp only [padY, middle, hs]
    omega
  have ht : padT (⟨z, v, r⟩ : FlagDegree) = r + v + z := by
    simp only [padT, total, hy]
    omega
  rw [hs, hy, ht]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_pos (r v z : ℕ)
    (hr : 2 ≤ r) (hv : 1 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_pos r v z 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v z 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 1) 131073 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131072 hr hv,
    paddedTail_raw_of_r_two_v_pos r v (z + 2) 131073 hr hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_one (r z : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 1 (z + 1) = rawCost r 1 z + rawCost r 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 1 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos r 1 z hr (by decide)

theorem rawCost_affine_of_r_two_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 2 v (z + 1) = rawCost 2 v z + rawCost 2 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 2⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 2 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_pos 2 v z (le_refl 2) (by omega)

theorem paddedTail_raw_of_r_one_v_two (v z d : ℕ) (hv : 2 ≤ v) :
    paddedTail (⟨z, v, 1⟩ : FlagDegree) d =
      ⟨2 * z * d, 1 + 2 * (v - 1) * d, 2 * d⟩ := by
  have hs : padS (⟨z, v, 1⟩ : FlagDegree) = 2 := by rfl
  have hy : padY (⟨z, v, 1⟩ : FlagDegree) = v + 1 := by
    unfold padY
    rw [hs]
    change max (v + 1) 3 = v + 1
    omega
  have ht : padT (⟨z, v, 1⟩ : FlagDegree) = v + 1 + z := by
    unfold padT
    rw [hy]
    change max (z + v + 1) (v + 1) = v + 1 + z
    omega
  change (⟨2 * (padT (⟨z, v, 1⟩ : FlagDegree) -
      padY ⟨z, v, 1⟩) * d,
    1 + 2 * (padY (⟨z, v, 1⟩ : FlagDegree) -
      padS ⟨z, v, 1⟩) * d,
    2 * (padS (⟨z, v, 1⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hz : v + 1 + z - (v + 1) = z := by omega
  have hvsub : v + 1 - 2 = v - 1 := by omega
  rw [hz, hvsub]

theorem paddedCost_raw_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * paddedCost 131072 131073 (⟨z + 1, v, 1⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, v, 1⟩ +
        paddedCost 131072 131073 ⟨z + 2, v, 1⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_one_v_two v z 131072 hv,
    paddedTail_raw_of_r_one_v_two v z 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 1) 131073 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131072 hv,
    paddedTail_raw_of_r_one_v_two v (z + 2) 131073 hv]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_one_v_two (v z : ℕ) (hv : 2 ≤ v) :
    2 * rawCost 1 v (z + 1) = rawCost 1 v z + rawCost 1 v (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, v, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_one_v_two v z hv

theorem paddedTail_raw_of_r_two_v_zero (r z d : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    paddedTail (⟨z, 0, r⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  have hs : padS (⟨z, 0, r⟩ : FlagDegree) = r := by
    unfold padS
    change max r 2 = r
    omega
  have hy : padY (⟨z, 0, r⟩ : FlagDegree) = r + 1 := by
    unfold padY middle
    rw [hs]
    change max (0 + r) (r + 1) = r + 1
    omega
  have ht : padT (⟨z, 0, r⟩ : FlagDegree) = r + z := by
    unfold padT total
    rw [hy]
    change max (z + 0 + r) (r + 1) = r + z
    omega
  change (⟨2 * (padT (⟨z, 0, r⟩ : FlagDegree) -
      padY ⟨z, 0, r⟩) * d,
    1 + 2 * (padY (⟨z, 0, r⟩ : FlagDegree) -
      padS ⟨z, 0, r⟩) * d,
    2 * (padS (⟨z, 0, r⟩ : FlagDegree) - 1) * d⟩ : FlagDegree) = _
  rw [ht, hy, hs]
  have hzsub : r + z - (r + 1) = z - 1 := by omega
  rw [hzsub]
  congr <;> omega

theorem paddedCost_raw_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * paddedCost 131072 131073 (⟨z + 1, 0, r⟩ : FlagDegree) =
      paddedCost 131072 131073 ⟨z, 0, r⟩ +
        paddedCost 131072 131073 ⟨z + 2, 0, r⟩ := by
  unfold paddedCost
  rw [paddedTail_raw_of_r_two_v_zero r z 131072 hr hz,
    paddedTail_raw_of_r_two_v_zero r z 131073 hr hz,
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 1) 131073 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131072 hr (by omega),
    paddedTail_raw_of_r_two_v_zero r (z + 2) 131073 hr (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_of_r_two_v_zero (r z : ℕ)
    (hr : 2 ≤ r) (hz : 1 ≤ z) :
    2 * rawCost r 0 (z + 1) = rawCost r 0 z + rawCost r 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  exact paddedCost_raw_affine_of_r_two_v_zero r z hr hz

theorem paddedTail_raw_r_two_v_zero_boundary (r d : ℕ) (hr : 2 ≤ r) :
    paddedTail (⟨0, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ ∧
      paddedTail (⟨1, 0, r⟩ : FlagDegree) d =
        ⟨0, 1 + 2 * d, 2 * (r - 1) * d⟩ := by
  constructor
  · unfold paddedTail padT padY padS middle total
    simp only [Nat.zero_add]
    have hm : max r 2 = r := by omega
    rw [hm]
    have hm' : max r (r + 1) = r + 1 := by omega
    rw [hm']
    norm_num
  · simpa using paddedTail_raw_of_r_two_v_zero r 1 d hr (by decide)

theorem rawCost_convex_r_two_v_zero_boundary (r : ℕ) (hr : 2 ≤ r) :
    2 * rawCost r 0 1 ≤ rawCost r 0 0 + rawCost r 0 2 := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, r⟩ : FlagDegree) := by
    intro h
    have hbad := h.2
    change r + 2 ≤ 0 + r at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn 0), if_neg (hn 1),
    if_neg (hn 2)]
  unfold paddedCost
  rw [(paddedTail_raw_r_two_v_zero_boundary r 131072 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).1,
    (paddedTail_raw_r_two_v_zero_boundary r 131072 hr).2,
    (paddedTail_raw_r_two_v_zero_boundary r 131073 hr).2,
    paddedTail_raw_of_r_two_v_zero r 2 131072 hr (by decide),
    paddedTail_raw_of_r_two_v_zero r 2 131073 hr (by decide)]
  unfold flagMixed
  ring_nf
  omega

theorem paddedTail_raw_r_one_v_one (z d : ℕ) (hz : 1 ≤ z) :
    paddedTail (⟨z, 1, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 1) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 2) 3 = z + 2 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_one (z : ℕ) :
    2 * rawCost 1 1 (z + 1) ≤ rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · have hzpos : 1 ≤ z := by omega
    have hEq : 2 * paddedCost 131072 131073
          (⟨z + 1, 1, 1⟩ : FlagDegree) =
        paddedCost 131072 131073 ⟨z, 1, 1⟩ +
          paddedCost 131072 131073 ⟨z + 2, 1, 1⟩ := by
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_one z 131072 hzpos,
        paddedTail_raw_r_one_v_one z 131073 hzpos,
        paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 1 = z := by omega
      have h2 : z + 2 - 1 = z + 1 := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 1) + 1 := by omega
      rw [hzsplit]
      simp only [Nat.add_sub_cancel]
      unfold flagMixed
      ring
    exact hEq.le

theorem paddedTail_raw_r_one_v_zero (z d : ℕ) (hz : 2 ≤ z) :
    paddedTail (⟨z, 0, 1⟩ : FlagDegree) d =
      ⟨2 * (z - 2) * d, 1 + 2 * d, 2 * d⟩ := by
  unfold paddedTail padT padY padS middle total
  norm_num
  have hm : max (z + 1) 3 = z + 1 := by omega
  rw [hm]
  congr <;> omega

theorem rawCost_convex_r_one_v_zero (z : ℕ) :
    2 * rawCost 1 0 (z + 1) ≤ rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  by_cases hz0 : z = 0
  · subst z
    norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
  · by_cases hz1 : z = 1
    · subst z
      norm_num [paddedCost, paddedTail, padT, padY, padS, middle, total, flagMixed]
    · have hz : 2 ≤ z := by omega
      unfold paddedCost
      rw [paddedTail_raw_r_one_v_zero z 131072 hz,
        paddedTail_raw_r_one_v_zero z 131073 hz,
        paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
        paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
      have h1 : z + 1 - 2 = z - 1 := by omega
      have h2 : z + 2 - 2 = z := by omega
      rw [h1, h2]
      have hzsplit : z = (z - 2) + 2 := by omega
      rw [hzsplit]
      norm_num
      unfold flagMixed
      ring_nf
      exact le_rfl

theorem rawCost_discreteConvex (r v z : ℕ) (hr : 1 ≤ r) :
    2 * rawCost r v (z + 1) ≤ rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_convex_r_one_v_zero z
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_convex_r_one_v_one z
      · exact (rawCost_affine_of_r_one_v_two v z (by omega)).le
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      by_cases hz : z = 0
      · subst z
        exact rawCost_convex_r_two_v_zero_boundary r hr2
      · exact (rawCost_affine_of_r_two_v_zero r z hr2 (by omega)).le
    · by_cases hv1 : v = 1
      · subst v
        exact (rawCost_affine_of_r_two_v_one r z hr2).le
      · by_cases hr3 : r = 2
        · subst hr3
          exact (rawCost_affine_of_r_two_v_two v z (by omega)).le
        · exact (rawCost_affine_of_hybrid r v z (by omega) (by omega)).le

theorem rawBelow_of_z_le (r v z₁ z₂ : ℕ) (hz : z₁ ≤ z₂) :
    Below (⟨z₁, v, r⟩ : FlagDegree) ⟨z₂, v, r⟩ := by
  change r ≤ r ∧ v + r ≤ v + r ∧ z₁ + v + r ≤ z₂ + v + r
  omega

theorem rawCost_mono_z (r v : ℕ) : Monotone (rawCost r v) := by
  intro z₁ z₂ hz
  have hb := rawBelow_of_z_le r v z₁ z₂ hz
  by_cases ha : HybridAppliesC2 (⟨z₁, v, r⟩ : FlagDegree)
  · have ha' : HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      rcases ha with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_pos ha, if_pos ha']
    exact hybridCostC2_mono hb
  · have ha' : ¬ HybridAppliesC2 (⟨z₂, v, r⟩ : FlagDegree) := by
      intro h
      apply ha
      rcases h with ⟨hr, hv⟩
      exact ⟨hr, hv⟩
    simp only [rawCost, ordinaryCostOf, if_neg ha, if_neg ha']
    exact paddedCost_mono 131072 131073 hb

def forwardDiff (f : ℕ → ℕ) (n : ℕ) : ℕ := f (n + 1) - f n

theorem forwardDiff_mono_of_discreteConvex
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hconvex : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2)) (n : ℕ) :
    forwardDiff f n ≤ forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  have hc := hconvex n
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem move_one_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (a b : ℕ) (hcross : forwardDiff f a ≤ forwardDiff g b) :
    f (a + 1) + g b ≤ f a + g (b + 1) := by
  have hfa := hf (Nat.le_add_right a 1)
  have hgb := hg (Nat.le_add_right b 1)
  unfold forwardDiff at hcross
  omega

theorem transfer_all_right
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hdf : ∀ n, forwardDiff f n ≤ forwardDiff f (n + 1))
    (hdg : ∀ n, forwardDiff g n ≤ forwardDiff g (n + 1)) :
    ∀ a b, forwardDiff f a ≤ forwardDiff g b →
      f (a + 1) + g b ≤ f 0 + g (a + 1 + b) := by
  intro a
  induction a with
  | zero =>
      intro b hcross
      simpa only [Nat.zero_add, Nat.add_comm] using
        move_one_right f g hf hg 0 b hcross
  | succ a ih =>
      intro b hcross
      have hcross' : forwardDiff f a ≤ forwardDiff g (b + 1) :=
        (hdf a).trans (hcross.trans (hdg b))
      calc
        f (a + 1 + 1) + g b ≤ f (a + 1) + g (b + 1) :=
          move_one_right f g hf hg (a + 1) b hcross
        _ ≤ f 0 + g (a + 1 + (b + 1)) := ih (b + 1) hcross'
        _ = f 0 + g (a + 1 + 1 + b) := by
          rw [show a + 1 + (b + 1) = a + 1 + 1 + b by omega]

theorem two_discreteConvex_endpoint
    (f g : ℕ → ℕ) (hf : Monotone f) (hg : Monotone g)
    (hcf : ∀ n, 2 * f (n + 1) ≤ f n + f (n + 2))
    (hcg : ∀ n, 2 * g (n + 1) ≤ g n + g (n + 2))
    (a b : ℕ) :
    f a + g b ≤ max (f (a + b) + g 0) (f 0 + g (a + b)) := by
  have hdf (n : ℕ) : forwardDiff f n ≤ forwardDiff f (n + 1) :=
    forwardDiff_mono_of_discreteConvex f hf hcf n
  have hdg (n : ℕ) : forwardDiff g n ≤ forwardDiff g (n + 1) :=
    forwardDiff_mono_of_discreteConvex g hg hcg n
  rcases a with _ | a
  · simpa only [Nat.zero_add] using
      (le_max_right (f b + g 0) (f 0 + g b))
  rcases b with _ | b
  · simpa only [Nat.add_zero] using
      (le_max_left (f (a + 1) + g 0) (f 0 + g (a + 1)))
  by_cases hcross : forwardDiff f a ≤ forwardDiff g (b + 1)
  · have h := transfer_all_right f g hf hg hdf hdg a (b + 1) hcross
    have h' : f (a + 1) + g (b + 1) ≤
        f 0 + g (a + 1 + (b + 1)) := h
    apply h'.trans
    apply le_max_of_le_right
    rfl
  · have hcross' : forwardDiff g b ≤ forwardDiff f (a + 1) :=
      (hdg b).trans ((Nat.lt_of_not_ge hcross).le.trans (hdf a))
    have h := transfer_all_right g f hg hf hdg hdf b (a + 1) hcross'
    have h' : f (a + 1) + g (b + 1) ≤
        f (b + 1 + (a + 1)) + g 0 := by
      simpa only [Nat.add_comm] using h
    have h'' : f (a + 1) + g (b + 1) ≤
        f ((a + 1) + (b + 1)) + g 0 := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    apply h''.trans
    apply le_max_of_le_left
    rfl

theorem rawCost_affine_r_one_v_one (z : ℕ) (hz : 1 ≤ z) :
    2 * rawCost 1 1 (z + 1) = rawCost 1 1 z + rawCost 1 1 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 1, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_one z 131072 hz,
    paddedTail_raw_r_one_v_one z 131073 hz,
    paddedTail_raw_r_one_v_one (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_one (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 1 = z := by omega
  have h2 : z + 2 - 1 = z + 1 := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 1) + 1 := by omega
  rw [hzsplit]
  simp only [Nat.add_sub_cancel]
  unfold flagMixed
  ring

theorem rawCost_affine_r_one_v_zero (z : ℕ) (hz : 2 ≤ z) :
    2 * rawCost 1 0 (z + 1) = rawCost 1 0 z + rawCost 1 0 (z + 2) := by
  have hn (x : ℕ) : ¬ HybridAppliesC2 (⟨x, 0, 1⟩ : FlagDegree) := by
    intro h
    have hbad := h.1
    change 3 ≤ 1 at hbad
    omega
  simp only [rawCost, ordinaryCostOf, if_neg (hn z), if_neg (hn (z + 1)),
    if_neg (hn (z + 2))]
  unfold paddedCost
  rw [paddedTail_raw_r_one_v_zero z 131072 hz,
    paddedTail_raw_r_one_v_zero z 131073 hz,
    paddedTail_raw_r_one_v_zero (z + 1) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 1) 131073 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131072 (by omega),
    paddedTail_raw_r_one_v_zero (z + 2) 131073 (by omega)]
  have h1 : z + 1 - 2 = z - 1 := by omega
  have h2 : z + 2 - 2 = z := by omega
  rw [h1, h2]
  have hzsplit : z = (z - 2) + 2 := by omega
  rw [hzsplit]
  norm_num
  unfold flagMixed
  ring

theorem rawCost_affine_step_from_two (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 2 ≤ z) :
    2 * rawCost r v (z + 1) = rawCost r v z + rawCost r v (z + 2) := by
  by_cases hr1 : r = 1
  · subst r
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_r_one_v_zero z hz
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_r_one_v_one z (by omega)
      · exact rawCost_affine_of_r_one_v_two v z (by omega)
  · have hr2 : 2 ≤ r := by omega
    by_cases hv0 : v = 0
    · subst v
      exact rawCost_affine_of_r_two_v_zero r z hr2 (by omega)
    · by_cases hv1 : v = 1
      · subst v
        exact rawCost_affine_of_r_two_v_one r z hr2
      · by_cases hr3 : r = 2
        · subst hr3
          exact rawCost_affine_of_r_two_v_two v z (by omega)
        · exact rawCost_affine_of_hybrid r v z (by omega) (by omega)

theorem forwardDiff_eq_next_of_affine
    (f : ℕ → ℕ) (hmono : Monotone f)
    (n : ℕ) (hstep : 2 * f (n + 1) = f n + f (n + 2)) :
    forwardDiff f n = forwardDiff f (n + 1) := by
  have h₀ := hmono (Nat.le_add_right n 1)
  have h₁ := hmono (Nat.le_add_right (n + 1) 1)
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem affine_formula_from_three
    (f : ℕ → ℕ) (hmono : Monotone f)
    (hstep : ∀ n, 2 ≤ n → 2 * f (n + 1) = f n + f (n + 2))
    (z : ℕ) (hz : 3 ≤ z) :
    f z = f 3 + (f 4 - f 3) * (z - 3) := by
  have hdiffStep (n : ℕ) (hn : 2 ≤ n) :
      forwardDiff f n = forwardDiff f (n + 1) :=
    forwardDiff_eq_next_of_affine f hmono n (hstep n hn)
  have hdiff : ∀ n, 3 ≤ n → forwardDiff f n = forwardDiff f 3 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => exact (hdiffStep n (by omega)).symm.trans ih
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hmn := hmono (Nat.le_add_right n 1)
      have hd := hdiff n hn
      have hd' : f (n + 1) - f n = f 4 - f 3 := by
        simpa only [forwardDiff, show 3 + 1 = 4 by decide] using hd
      calc
        f (n + 1) = f n + (f (n + 1) - f n) :=
          (Nat.add_sub_of_le hmn).symm
        _ = f n + (f 4 - f 3) := by rw [hd']
        _ = (f 3 + (f 4 - f 3) * (n - 3)) + (f 4 - f 3) := by
          rw [ih]
        _ = f 3 + (f 4 - f 3) * (n + 1 - 3) := by
          have hnsub : n + 1 - 3 = (n - 3) + 1 := by omega
          rw [hnsub]
          ring

theorem rawCost_affine_from_three (r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    rawCost r v z = rawCost r v 3 +
      (rawCost r v 4 - rawCost r v 3) * (z - 3) := by
  exact affine_formula_from_three (rawCost r v) (rawCost_mono_z r v)
    (fun n hn => rawCost_affine_step_from_two r v n hr hn) z hz

end ProximityPrize.SubmissionLower.LocatorOrdinaryZConvex
end PackedLocator_LocatorOrdinaryZConvex

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration. -/
section PackedLocator_LocatorOrdinaryConcentration

/-!
# Concentrating ordinary-factor excess total degree

Discrete convexity lets all raw `z` weight in a finite nonempty family be
moved to one carrier without decreasing the upper bound.  This reduces the
three-coordinate ordinary partition problem to a two-coordinate zero-`z`
knapsack plus one carrier line.
-/

namespace ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration

open scoped BigOperators
open LocatorOrdinaryZConvex

set_option autoImplicit false

theorem exists_z_carrier
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (r v z : ι → ℕ)
    (hr : ∀ i ∈ s, 1 ≤ r i) (hne : s.Nonempty) :
    ∃ c ∈ s,
      (∑ i ∈ s, rawCost (r i) (v i) (z i)) ≤
        rawCost (r c) (v c) (∑ i ∈ s, z i) +
          ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by
  induction s using Finset.induction_on with
  | empty => simp at hne
  | @insert a s ha ih =>
      by_cases hs : s = ∅
      · subst s
        refine ⟨a, by simp, ?_⟩
        simp
      · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨c, hc, hbound⟩ := ih (fun i hi => hr i (by simp [hi])) hsne
        have hra : 1 ≤ r a := hr a (by simp)
        have hrc : 1 ≤ r c := hr c (by simp [hc])
        have hpair := two_discreteConvex_endpoint
          (rawCost (r a) (v a)) (rawCost (r c) (v c))
          (rawCost_mono_z (r a) (v a)) (rawCost_mono_z (r c) (v c))
          (fun n => rawCost_discreteConvex (r a) (v a) n hra)
          (fun n => rawCost_discreteConvex (r c) (v c) n hrc)
          (z a) (∑ i ∈ s, z i)
        have hpre :
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
              rawCost (r a) (v a) (z a) +
                (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := by
          rw [Finset.sum_insert ha]
          exact Nat.add_le_add_left hbound _
        by_cases hend :
            rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                rawCost (r c) (v c) 0 ≤
              rawCost (r a) (v a) 0 +
                rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)
        · refine ⟨c, by simp [hc], ?_⟩
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) := by
            exact hpair.trans (by simpa [max_eq_right hend])
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) 0 +
                  rawCost (r c) (v c) (z a + ∑ i ∈ s, z i)) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r c) (v c) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase c,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
              have hac : a ≠ c := fun h => ha (h ▸ hc)
              rw [Finset.erase_insert_of_ne hac, Finset.sum_insert]
              · ac_rfl
              · exact fun h => ha (Finset.mem_of_mem_erase h)
        · refine ⟨a, by simp, ?_⟩
          have hreverse :
              rawCost (r c) (v c) (z a + ∑ i ∈ s, z i) +
                  rawCost (r a) (v a) 0 ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            omega
          have htwo :
              rawCost (r a) (v a) (z a) +
                  rawCost (r c) (v c) (∑ i ∈ s, z i) ≤
                rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0 := by
            exact hpair.trans (by
              rw [max_eq_left]
              simpa [Nat.add_comm] using hreverse)
          have hzeros :
              rawCost (r c) (v c) 0 +
                  ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 =
                ∑ i ∈ s, rawCost (r i) (v i) 0 := by
            simpa only [Nat.add_comm] using
              (Finset.sum_erase_add s
                (fun i => rawCost (r i) (v i) 0) hc)
          calc
            (∑ i ∈ insert a s, rawCost (r i) (v i) (z i)) ≤
                rawCost (r a) (v a) (z a) +
                  (rawCost (r c) (v c) (∑ i ∈ s, z i) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0) := hpre
            _ ≤ (rawCost (r a) (v a) (z a + ∑ i ∈ s, z i) +
                  rawCost (r c) (v c) 0) +
                    ∑ i ∈ s.erase c, rawCost (r i) (v i) 0 := by omega
            _ = rawCost (r a) (v a) (∑ i ∈ insert a s, z i) +
                  ∑ i ∈ (insert a s).erase a,
                    rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha, Finset.erase_insert ha]
              rw [← hzeros]
              ac_rfl

end ProximityPrize.SubmissionLower.LocatorOrdinaryConcentration
end PackedLocator_LocatorOrdinaryConcentration

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Audit. -/
section PackedLocator_LocatorPhase6800Audit

/-!
# Soundness utilities for the compact 6800 phase receipt

These lemmas are deliberately separate from the generated receipt data.  The
first records the correlated (rather than independent-maxima) initial-A
ledger.  The remaining lemmas justify interpreting a checked threshold row as
an exact routeability cutoff in the raw total coordinate.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Audit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000


/-- Taking one more high-band projection only adds a nonnegative summand. -/
theorem powerBandBudget_le_succ
    (delta dT dY dS T YS S k : ℕ) :
    powerBandBudget delta dT dY dS T YS S k ≤
      powerBandBudget delta dT dY dS T YS S (k + 1) := by
  induction k generalizing T YS S with
  | zero =>
      simp only [powerBandBudget, Nat.zero_add]
      exact Nat.zero_le _
  | succ k ih =>
      simp only [powerBandBudget]
      exact Nat.add_le_add_left
        (ih (T := T - dT) (YS := YS - dY) (S := S - dS)) _

/-- The cumulative high-band cost is monotone in the number of projections. -/
theorem powerBandBudget_mono_fuel
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    powerBandBudget delta dT dY dS T YS S k₁ ≤
      powerBandBudget delta dT dY dS T YS S k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        powerBandBudget delta dT dY dS T YS S k₁ ≤
            powerBandBudget delta dT dY dS T YS S (k₁ + d) :=
          ih (Nat.le_add_right _ _)
        _ ≤ powerBandBudget delta dT dY dS T YS S ((k₁ + d) + 1) :=
          powerBandBudget_le_succ delta dT dY dS T YS S (k₁ + d)
        _ = powerBandBudget delta dT dY dS T YS S (k₁ + d.succ) := by
          congr 1

/-- For fixed raw slope and middle coordinates, increasing `z` can only make
the source route easier: the residual total box and the fuel both decrease. -/
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have hr' : 1 ≤ r := by simpa only [rawFlag_all] using hr
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      powerBandBudget 50293 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50293 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50293
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50293 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50293 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50293 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · rcases hband with hband | hthin
    · left
      unfold SourceNumbers.band at hband ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
      exact (hsameFuel.trans hmoreFuel).trans_lt hband
    · right
      have hsameFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₂)) 50293
              (contactDec (rawFlag r v z₂)) (r + v + z₂) (r + v) r
              (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
        have hcap : s.contactCap (rawFlag r v z₂) = s.contactCap (rawFlag r v z₁) := by
          simp only [SourceNumbers.contactCap, contactDec, rawFlag_middle, rawFlag_all]
        have hdec : contactDec (rawFlag r v z₂) = contactDec (rawFlag r v z₁) := by
          simp only [contactDec, rawFlag_middle, rawFlag_all]
        rw [hcap, hdec]
        exact powerBandBudgetThin_mono 131071 50293 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r)
          le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
        powerBandBudgetThin_mono_fuel 131071 (s.contactCap (rawFlag r v z₁)) 50293
          (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r) hfuel
      unfold SourceNumbers.bandThin at hthin ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin


/-! ## Noncircular semantics of a prefix receipt -/

theorem sumFlag_rawBelow_of_subset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊆ A) :
    RawBelow (sumFlag U flag) (sumFlag A flag) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Finset.sum_le_sum_of_subset_of_nonneg hUA
      (fun _ _ _ ↦ Nat.zero_le _)

/-- A proper subfamily has strictly smaller raw slope when every factor has
positive slope.  This is the well-founded coordinate behind `afterR = r-1`. -/
theorem sumFlag_all_lt_of_ssubset
    {ι : Type} [DecidableEq ι] (flag : ι → FlagDegree)
    {A U : Finset ι} (hUA : U ⊂ A)
    (hpositive : ∀ i ∈ A, 1 ≤ (flag i).all) :
    (sumFlag U flag).all < (sumFlag A flag).all := by
  have hdiff : (A \ U).Nonempty := by
    exact Finset.sdiff_nonempty.mpr (fun hAU ↦ hUA.ne (Finset.Subset.antisymm hUA.subset hAU))
  obtain ⟨i, hi⟩ := hdiff
  have hiA : i ∈ A := (Finset.mem_sdiff.mp hi).1
  have hiOne : 1 ≤ (flag i).all := hpositive i hiA
  have hiSum : (flag i).all ≤ ∑ j ∈ A \ U, (flag j).all := by
    exact Finset.single_le_sum
      (f := fun j ↦ (flag j).all) (fun _ _ ↦ Nat.zero_le _) hi
  have hsplit := Finset.sum_sdiff hUA.subset (f := fun j ↦ (flag j).all)
  simp only [sumFlag_all] at *
  omega

/-- Additivity of every numerical phase potential on a finite family. -/
theorem sum_potential_eval
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    (flag : ι → FlagDegree) (q : Potential) :
    (∑ i ∈ s, q.eval (flag i)) = q.eval (sumFlag s flag) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Semantic content of one cumulative prefix table.  `terminal` checks only
actual nonrouteable states.  `monotone` records the cumulative max closure in
raw `r`, `v`, and `z`; neither field assumes the desired phase bound. -/
structure PrefixTableSound
    (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) (pref : FlagDegree → ℕ) : Prop where
  terminal : ∀ p, ¬ routeable p →
    previous p ≤ q.eval p + pref p
  monotone : ∀ {p₁ p₂}, RawBelow p₁ p₂ → pref p₁ ≤ pref p₂

/-- A parent of raw slope `r` queries the prefix after completing slope
`r-1`.  The subtraction is harmless at zero; routed nonempty products have
positive slope. -/
def parentDefect (pref : FlagDegree → ℕ) (parent : FlagDegree) : ℕ :=
  pref (rawFlag (parent.all - 1) parent.yz parent.zOnly)

/-- The value after adjoining one source phase. -/
def applyPhase (previous : FlagDegree → ℕ) (q : Potential)
    (routeable : FlagDegree → Prop) [DecidablePred routeable]
    (pref : FlagDegree → ℕ)
    (p : FlagDegree) : ℕ :=
  if routeable p then
    min (previous p) (q.eval p + parentDefect pref p)
  else previous p

/-- A cumulative prefix row bounds every nonrouteable strict child of its
parent.  This is the exact semantic fact needed by the algebraic batch split. -/
theorem terminal_le_parent_charge
    {previous pref : FlagDegree → ℕ} {q : Potential}
    {routeable : FlagDegree → Prop}
    (hrows : PrefixTableSound previous q routeable pref)
    {child parent : FlagDegree} (hbelow : RawBelow child parent)
    (hslope : child.all < parent.all) (hterminal : ¬ routeable child) :
    previous child ≤ q.eval child + parentDefect pref parent := by
  have hpred : RawBelow child
      (rawFlag (parent.all - 1) parent.yz parent.zOnly) := by
    rcases hbelow with ⟨hr, hv, hz⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [rawFlag_all]
      using (show child.all ≤ parent.all - 1 by omega)
    · simpa only [rawFlag] using hv
    · simpa only [rawFlag] using hz
  simpa only [parentDefect] using (hrows.terminal child hterminal).trans
    (Nat.add_le_add_left (hrows.monotone hpred) _)


/-- A threshold function is semantically checked by boundary receipts at
every raw `(r,v)` row. -/
def ThresholdTableSound (s : SourceNumbers)
    (threshold : ℕ → ℕ → ℕ) : Prop :=
  ∀ r v, 1 ≤ r → r + v ≤ 135 →
    thresholdBoundary s r v (threshold r v)


/-! ## State-local base semantics -/

/-- The zero-`z` two-coordinate table.  The zero-slope state represents the
empty family; positive-slope states are the `z = 0` entries of the base rows. -/
def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)


/-- The sole semantic arithmetic condition required of the compact base
table.  It is finite on the benchmark box.  For every possible carrier
`(r,v)`, the row for the aggregate `(R,V)` dominates that carrier with all
remaining factors charged to the zero-`z` table. -/
def BaseCandidatesSound (rows : Array BaseRow) : Prop :=
  ∀ R V r v z,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 29 → R + V ≤ 135 →
    (r < R ∨ v = V) → R + V + z ≤ 6677 →
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z)

/-- Slope of the carrier's affine ordinary-cost tail, valid from `z = 3`. -/
def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

/-- Carrier line after adding the exact zero-`z` residual-table value. -/
def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

theorem carrierCost_eq_candidateLine
    (rows : Array BaseRow) (R V r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) =
      candidateLine rows R V r v z := by
  rw [LocatorOrdinaryZConvex.rawCost_affine_from_three r v z hr hz]
  unfold candidateLine candidateSlope
  omega

theorem candidateLine_shift
    (rows : Array BaseRow) (R V r v start z : ℕ)
    (hstart : 3 ≤ start) (hz : start ≤ z) :
    candidateLine rows R V r v z =
      candidateLine rows R V r v start + candidateSlope r v * (z - start) := by
  unfold candidateLine
  have hsplit : z - 3 = (start - 3) + (z - start) := by omega
  rw [hsplit, Nat.mul_add]
  omega

/-- Two affine natural-number functions ordered at the left endpoint remain
ordered when the lower function has no larger slope. -/
theorem affine_le_of_start_and_slope
    (a A m M d : ℕ) (ha : a ≤ A) (hm : m ≤ M) :
    a + m * d ≤ A + M * d := by
  exact Nat.add_le_add ha (Nat.mul_le_mul_right d hm)

/-- Endpoint domination suffices on a finite interval even when the candidate
line has the larger slope. -/
theorem affine_le_between
    (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A)
    (hend : a + m * finish ≤ A + M * finish) :
    a + m * d ≤ A + M * d := by
  by_cases hm : m ≤ M
  · exact affine_le_of_start_and_slope a A m M d hstart hm
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M + (m - M) = m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a + (m - M) * finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta : (m - M) * d ≤ (m - M) * finish :=
      Nat.mul_le_mul_left (m - M) hd
    rw [← hdecomp, Nat.add_mul]
    omega

theorem candidateLine_le_segment_of_start_and_slope
    (rows : Array BaseRow) (R V r v z : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hslope : candidateSlope r v ≤ s.slope) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  unfold BaseSegment.evalAt
  exact affine_le_of_start_and_slope _ _ _ _ _ hstart hslope

theorem candidateLine_le_segment_between
    (rows : Array BaseRow) (R V r v z finish : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z) (hzf : z ≤ finish)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hfinish : candidateLine rows R V r v finish ≤ s.evalAt finish) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  have hsf : s.start ≤ finish := hsz.trans hzf
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  rw [candidateLine_shift rows R V r v s.start finish hs3 hsf] at hfinish
  unfold BaseSegment.evalAt at hfinish ⊢
  apply affine_le_between _ _ _ _ _ _
  · exact Nat.sub_le_sub_right hzf s.start
  · exact hstart
  · exact hfinish
end ProximityPrize.SubmissionLower.LocatorPhase6800Audit
end PackedLocator_LocatorPhase6800Audit
end Compact_PackedLocatorTail
