import ProximityPrize.SubmissionLower.LocatorGenericPowerRoute6803
import ProximityPrize.SubmissionLower.LocatorPhase6803SourceSound

/-!
# Semantic view of the 68.03 phase oracle

The generated numerical oracle predates the retuned algebraic power route, so
its exact route box uses the 68.02 route-box type.  Those structures have the
same fields but are nominally distinct.  This module transports the checked
68.03 source bounds to the route-box and helper-gate types consumed by the
68.03 semantic proof.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803SemanticOracle

open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential sumFlag)

set_option autoImplicit false

def exactRouteBox (p : FlagDegree) :
    LocatorGenericPowerRoute6803.PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

/-- State-local base certificate over the enlarged 68.03 degree box. -/
def StateLocalBaseOracleSound (baseCap : FlagDegree → ℕ) : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree),
    (∀ i ∈ s, 1 ≤ (p i).all) →
    (sumFlag s p).all ≤ 29 → middle (sumFlag s p) ≤ 135 →
    total (sumFlag s p) ≤ 6676 →
    (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) ≤
      baseCap (sumFlag s p)

/-- Componentwise raw containment used by the 68.03 defect recurrence. -/
def RawBelow (q p : FlagDegree) : Prop :=
  q.all ≤ p.all ∧ q.yz ≤ p.yz ∧ q.zOnly ≤ p.zOnly

def RawStrictSlopeBelow (q p : FlagDegree) : Prop :=
  RawBelow q p ∧ q.all < p.all

/-- Semantic defect condition over the enlarged 68.03 degree box. -/
def PhaseDefectSound (previousCap : FlagDegree → ℕ)
    (source : LocatorPhase6803Oracle.SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p q, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric cap recurrence represented by a checked 68.03 phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : LocatorPhase6803Oracle.SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p

structure PhaseSourceSound where
  source : LocatorPhase6803Oracle.SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    j ≤ source.fuel p →
    LocatorGenericPowerRoute6803.stageCost source.totalCap source.middleCap
      source.slopeCap (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    j ≤ source.fuel p →
    LocatorGenericHelperFactorSwitch6803.HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

def ofNumeric (sound : LocatorPhase6803Oracle.PhaseSourceSound) :
    PhaseSourceSound where
  source := sound.source
  potential := sound.potential
  stageCost_le p j hr hs hy ht hj := by
    have h := sound.stageCost_le p j hr hs hy ht hj
    simpa only [LocatorGenericPowerRoute6803.stageCost,
      LocatorGenericPowerRoute6803.stagePair,
      LocatorGenericHelperFactorSwitch6803.helperPair,
      LocatorPhase6803Oracle.stageCost, LocatorPhase6803Oracle.stagePair,
      LocatorPhase6803Oracle.helperPair, exactRouteBox,
      LocatorPhase6803Oracle.exactRouteBox] using h
  stageGates p j hr hs hy ht hj := by
    have h := sound.stageGates p j hr hs hy ht hj
    simpa only [LocatorGenericHelperFactorSwitch6803.HelperPairGates,
      LocatorGenericHelperFactorSwitch6803.helperPair,
      LocatorPhase6803Oracle.HelperPairGates,
      LocatorPhase6803Oracle.helperPair] using h

def r1200Sound : PhaseSourceSound :=
  ofNumeric LocatorPhase6803SourceSound.r1200Sound

def sourceCSound : PhaseSourceSound :=
  ofNumeric LocatorPhase6803SourceSound.sourceCSound

def split500Sound : PhaseSourceSound :=
  ofNumeric LocatorPhase6803SourceSound.split500Sound

def phase4Sound : PhaseSourceSound :=
  ofNumeric LocatorPhase6803SourceSound.phase4Sound

end ProximityPrize.SubmissionLower.LocatorPhase6803SemanticOracle
