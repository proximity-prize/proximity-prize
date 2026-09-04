import ProximityPrize.SubmissionLower.LocatorGenericPowerRoute

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Oracle. -/
section PackedLocator_LocatorPhase6800Oracle

/-!
# Compact numerical oracle for the 6800 regular-factor phases

This module contains only the small, reusable interface of the numerical
certificate.  The generated receipt rows live in separate modules.  A raw
state `⟨z,v,r⟩` represents cumulative degrees
`(total, middle, slope) = (z+v+r,v+r,r)`.

The four source phases are, in order, R1200, C, Split500 and Split390.  Three
prefixes forget `z`.  The C prefix retains 304-wide buckets (offset 64) only
on the critical rectangle `r ≤ 17, v ≤ 64`; outside that rectangle it too
forgets `z`.  This is a sound weakening of the exact prefix recurrence.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Oracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorLowQuotient LocatorArbitraryPowerAvoidance
open LocatorGenericPowerRoute LocatorGenericHelperFactorSwitch

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Coefficients of an additive potential in cumulative coordinates. -/
structure Potential where
  totalCoeff : ℕ
  middleCoeff : ℕ
  slopeCoeff : ℕ
  deriving DecidableEq, Repr

def Potential.eval (q : Potential) (p : FlagDegree) : ℕ :=
  q.totalCoeff * total p + q.middleCoeff * middle p + q.slopeCoeff * p.all

theorem Potential.eval_add (q : Potential) (p₁ p₂ : FlagDegree) :
    q.eval (p₁ + p₂) = q.eval p₁ + q.eval p₂ := by
  simp only [Potential.eval, total, middle, add_zOnly, add_yz, add_all]
  ring

def initialAPotential : Potential :=
  ⟨5961153504, 5974067721865, 22929595672934⟩

def r1200Potential : Potential :=
  ⟨13427087260899, 663874773565556, 2979865684813599⟩

def sourceCPotential : Potential :=
  ⟨838515060584, 41471165784403, 186185626057566⟩

def split500Potential : Potential :=
  ⟨585232039360, 17772798151495, 79353607227622⟩

def split390Potential : Potential :=
  ⟨88177732979, 3190112842069, 14358837685870⟩

/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def sourceR1200 : SourceNumbers :=
  ⟨328400, 6642, 1480, 5227117860923383312⟩

def sourceC : SourceNumbers :=
  ⟨82100, 1660, 370, 18811500529412710⟩

def sourceSplit500 : SourceNumbers :=
  ⟨42000, 1383, 310, 4161068143836058⟩

def sourceSplit390 : SourceNumbers :=
  ⟨19500, 539, 120, 95423319727890⟩

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50303 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50303 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50303 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

theorem SourceNumbers.bandThin_le (s : SourceNumbers) (p : FlagDegree) :
    s.bandThin p ≤ s.band p :=
  powerBandBudgetThin_le _ _ _ _ _ _ _ _ _ _ _

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def exactRouteBox (p : FlagDegree) : PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

/-- The arithmetic interface required by the algebraic source adapter.  The
stage-cost and gate checks are deliberately separate from band thresholds. -/
structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

/-- Raw-to-cumulative flag constructor. -/
def rawFlag (r v z : ℕ) : FlagDegree := ⟨z, v, r⟩

@[simp] theorem rawFlag_all (r v z : ℕ) : (rawFlag r v z).all = r := rfl
@[simp] theorem rawFlag_middle (r v z : ℕ) : middle (rawFlag r v z) = r + v := by
  simp [rawFlag, middle, Nat.add_comm]
@[simp] theorem rawFlag_total (r v z : ℕ) : total (rawFlag r v z) = r + v + z := by
  simp [rawFlag, total, Nat.add_comm, Nat.add_left_comm]

/-- The C-prefix bucket used by the compact receipt. -/
def cBucket (z : ℕ) : ℕ := if z ≤ 64 then 0 else (z - 64 + 303) / 304

theorem cBucket_le_21 (z : ℕ) (hz : z ≤ 6412) : cBucket z ≤ 21 := by
  unfold cBucket
  split <;> omega

/-- Exact maximum additive A-potential available to a complementary raw flag
inside the wide cumulative box `(6412,153,33)`. -/
def initialAComplement (p : FlagDegree) : ℕ :=
  let t := 6412 - total p
  let y := 153 - middle p
  let r := 33 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAPotential.eval (rawFlag nr nv (t' - nv))

/-- The greedy complement is maximal for the A potential among all raw flags
that can be added to `p` inside the wide box. -/
theorem initialAPotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 6412)
    (hy : middle p + middle n ≤ 153)
    (hr : p.all + n.all ≤ 33) :
    initialAPotential.eval n ≤ initialAComplement p := by
  have hnpY : n.all ≤ middle n := by simp [middle]
  have hnpT : middle n ≤ total n := by simp [middle, total]
  have hppY : p.all ≤ middle p := by simp [middle]
  have hppT : middle p ≤ total p := by simp [middle, total]
  simp only [initialAComplement, Potential.eval, initialAPotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega

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
theorem initialA_helpers_sum_le_complement
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 6412)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 153)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 33) :
    (∑ i ∈ s, helper i) ≤ initialAComplement universal := by
  calc
    (∑ i ∈ s, helper i) ≤ ∑ i ∈ s, initialAPotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi => hhelper i hi)
    _ = initialAPotential.eval (sumFlag s p) := sum_initialAPotential_eval s p
    _ ≤ initialAComplement universal := by
      apply initialAPotential_le_complement
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr

/-- A threshold row says at which `z` each source becomes routeable for fixed
positive slope `r` and residual middle coordinate `v`. -/
structure ThresholdReceipt where
  r : ℕ
  v : ℕ
  r1200 : ℕ
  sourceC : ℕ
  split500 : ℕ
  split390 : ℕ
  deriving DecidableEq, Repr

def thresholdBoundary (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  let maxZ := 6412 - (r + v)
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
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 132 ∧
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
  split390 : ℕ
  deriving DecidableEq, Repr

def PrefixReceipt.ExpectedShape (q : PrefixReceipt) : Prop :=
  1 ≤ q.afterR ∧ q.afterR ≤ 28 ∧ q.afterR + 1 + q.v ≤ 132 ∧
    q.sourceC.length = (if q.afterR ≤ 0 ∧ q.v ≤ 64 then 22 else 1)

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
`v`, over `1 ≤ r ≤ 29` and `r+v ≤ 132`. -/
def baseRowIndex (r v : ℕ) : ℕ :=
  (r - 1) * 133 - ((r - 1) * r) / 2 + v

def defaultBaseRow : BaseRow := ⟨0, 0, 0, 0, 0, []⟩

def lookupBaseRow (rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  (rows[baseRowIndex r v]?).getD defaultBaseRow

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def BaseRowsIndexed (rows : Array BaseRow) : Prop :=
  rows.size = 3422 ∧
    ∀ r ∈ (List.range 29).map (fun q => q + 1),
      ∀ v ∈ List.range (133 - r),
        let q := lookupBaseRow rows r v
        q.r = r ∧ q.v = v

instance (rows : Array BaseRow) : Decidable (BaseRowsIndexed rows) := by
  unfold BaseRowsIndexed
  infer_instance

def BaseRow.ExpectedShape (q : BaseRow) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 132 ∧
    q.segments ≠ [] ∧ q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start) ∧
    ∀ s ∈ q.segments, s.start ≤ 6412 - (q.r + q.v)

instance (q : BaseRow) : Decidable q.ExpectedShape := by
  unfold BaseRow.ExpectedShape
  infer_instance

/-- State-local form of the base certificate.  Unlike the legacy full-box
interface below, this preserves the aggregate flag needed by every phase
transition. -/
def StateLocalBaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree),
    (∀ i ∈ s, 1 ≤ (p i).all) →
    (sumFlag s p).all ≤ 29 → middle (sumFlag s p) ≤ 132 →
    total (sumFlag s p) ≤ 6412 →
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
  ∀ p q, p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric recurrence represented by a checked phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p

/-- Abstract base certificate.  This isolates the discrete-convexity and the
two-coordinate unbounded knapsack proof from the algebraic phase consumer. -/
def BaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (p : ι → FlagDegree),
    (∀ i, 1 ≤ (p i).all) →
    (∑ i, (p i).all) ≤ 29 →
    (∑ i, middle (p i)) ≤ 132 →
    (∑ i, total (p i)) ≤ 6412 →
    (∑ i, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap ⟨6412 - 132, 132 - 30, 30⟩

/-- Consumer-facing abstraction: numerical receipt checking yields a narrow
phase cap, while the algebraic batch route supplies the phase transitions. -/
structure CheckedPhaseOracle where
  narrowCap : FlagDegree → ℕ
  baseCap : FlagDegree → ℕ
  baseSound : BaseOracleSound baseCap
  narrow_le : ∀ p, p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    narrowCap p ≤ 254118829368535504
  joint_le : ∀ p, p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6412 →
    narrowCap p + initialAComplement p ≤ 254595720129422441

/-! ## Generic finite-set transition consumed by the batch route -/

/-- A prefix defect converts a strict batch split into the next phase bound.
This is the exact bookkeeping used by every one of the four source phases;
all source-specific algebra is confined to `hchild` and `hexit`. -/
theorem phase_split_le
    {ι : Type} [DecidableEq ι]
    (A U : Finset ι) (flag : ι → FlagDegree) (count : ι → ℕ)
    (q : Potential)
    (childCap defect parentPotential : ℕ)
    (hsub : U ⊆ A)
    (hchild : (∑ i ∈ U, count i) ≤ childCap)
    (hexit : ∀ i ∈ A \ U, count i ≤ q.eval (flag i))
    (hprefix : childCap ≤ (∑ i ∈ U, q.eval (flag i)) + defect)
    (hparent : (∑ i ∈ A, q.eval (flag i)) + defect ≤ parentPotential) :
    (∑ i ∈ A, count i) ≤ parentPotential := by
  have hdisjoint : Disjoint U (A \ U) := by
    apply Finset.disjoint_left.mpr
    intro i hiU hiD
    exact (Finset.mem_sdiff.mp hiD).2 hiU
  have hsplit : A = U ∪ (A \ U) := by
    exact (Finset.union_sdiff_of_subset hsub).symm
  rw [hsplit, Finset.sum_union hdisjoint]
  have hexitSum : (∑ i ∈ A \ U, count i) ≤
      ∑ i ∈ A \ U, q.eval (flag i) :=
    Finset.sum_le_sum (fun i hi => hexit i hi)
  have hcombined : (∑ i ∈ U, count i) + (∑ i ∈ A \ U, count i) ≤
      ((∑ i ∈ U, q.eval (flag i)) + (∑ i ∈ A \ U, q.eval (flag i))) +
        defect := by
    omega
  have hpotentialSplit : (∑ i ∈ A, q.eval (flag i)) =
      (∑ i ∈ U, q.eval (flag i)) +
        (∑ i ∈ A \ U, q.eval (flag i)) := by
    rw [Nat.add_comm]
    exact (Finset.sum_sdiff hsub).symm
  rw [hpotentialSplit] at hparent
  exact hcombined.trans hparent

def certifiedNarrowMaximum : ℕ := 254118829368535504
def certifiedJointMaximum : ℕ := 254595720129422441
def tightenedRegularAllowance : ℕ := 257395272113379213

theorem certifiedJoint_lt_allowance :
    certifiedJointMaximum < tightenedRegularAllowance := by decide

theorem certifiedJoint_slack :
    tightenedRegularAllowance - certifiedJointMaximum = 2799551983956772 := by
  decide

/-- Arithmetic end of the initial-A ledger.  The two hypotheses are the only
set-dependent facts required from the structural bridge. -/
theorem initialA_sum_le_certifiedJoint
    (phaseSum helperSum : ℕ) (p : FlagDegree)
    (hphase : phaseSum ≤ certifiedNarrowMaximum)
    (hhelper : helperSum ≤ certifiedJointMaximum - certifiedNarrowMaximum) :
    phaseSum + helperSum ≤ certifiedJointMaximum := by
  unfold certifiedNarrowMaximum certifiedJointMaximum at *
  omega

end ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
end PackedLocator_LocatorPhase6800Oracle

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier14 : True := by trivial
end ProximityPrize.SubmissionLower

