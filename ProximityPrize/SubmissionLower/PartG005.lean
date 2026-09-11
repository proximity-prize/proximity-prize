import ProximityPrize.SubmissionLower.PartG004


section Compact_Oracle80791
/-! Error-80791 phase ingredient, adapted from the promoted shared-product machinery.
No protocol claim is asserted in this module. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80791.PowerRoute Lower80791.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000
/-- The cumulative boxes used by a power source. -/
structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50283 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

/-- Lever S1.  The product of the routed factors has contact weight at least
`131071 * middle p - p.all` (`contact_ge_ys` with the exact aggregate weights), and the
source's kernel degree satisfies `D + slopeCap ≤ 131071 * (middleCap + 1)`; so the level-1
contact cap of the band ladder is at most `contactCap`, and it drops by `50283 + contactDec`
per level.  `bandThin` is the ladder charged on the rows that can carry a monomial. -/
def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50283 (contactDec p)
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
    1 ≤ p.all → p.all ≤ 30 → middle p ≤ 136 → total p ≤ 6917 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 30 → middle p ≤ 136 → total p ≤ 6917 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

/-- Semantic condition checked by one phase's prefix table.  At a routeable
parent, every strict nonrouteable stopping child is paid by the stored defect.
The algebraic batch engine turns precisely this condition into the phase cap.
-/
def PhaseDefectSound (previousCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p q, p.all ≤ 30 → middle p ≤ 136 → total p ≤ 6917 →
    RawStrictSlopeBelow q p → ¬source.Routeable q →
    previousCap q ≤ potential.eval q + defect p

/-- Numeric recurrence represented by a checked phase table. -/
def PhaseCapEquation (previousCap nextCap : FlagDegree → ℕ)
    (source : SourceNumbers) (potential : Potential)
    (defect : FlagDegree → ℕ) : Prop :=
  ∀ p, p.all ≤ 30 → middle p ≤ 136 → total p ≤ 6917 →
    nextCap p = if source.Routeable p then
      min (previousCap p) (potential.eval p + defect p)
    else previousCap p


end ProximityPrize.SubmissionLower.Lower80791.Oracle

end Compact_Oracle80791
