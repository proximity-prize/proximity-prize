import ProximityPrize.SubmissionLower.LocatorPhase6800Oracle
import ProximityPrize.SubmissionLower.LocatorPhase4Source6803

/-!
# Numerical interface for a four-phase 68.03 receipt

This deliberately lives beside, rather than modifies, the checked 68.02
oracle.  The old oracle fixes agreement `181373`, band decrement `50303`, and
the cumulative box `(6412,132,29)`.  The definitions below record the exact
68.03 replacements needed by a regenerated receipt.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803Oracle

open RCN095 RCN260 LocatorFactorAggregate
open LocatorArbitraryPowerAvoidance
open LocatorGenericHelperFactorSwitch
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false

def helperPair (L YS S leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363, leftY, leftR, leftZ, YS, S, L⟩

def HelperPairGates (L YS S leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair L YS S leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

def stagePair (L YS S : ℕ) (b : LocatorGenericPowerRoute.PowerRouteBox)
    (j : ℕ) : UnequalParameters :=
  helperPair (L - j * b.tLo) (YS - j * b.yLo) (S - j * b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S : ℕ) (b : LocatorGenericPowerRoute.PowerRouteBox)
    (j : ℕ) : ℕ :=
  (stagePair L YS S b j).regularCountCap

def exactRouteBox (p : FlagDegree) : LocatorGenericPowerRoute.PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

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
  powerBandBudget 50293 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50293 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) := by
  unfold SourceNumbers.Routeable
  infer_instance

def r1200Potential : Potential :=
  ⟨13427735141811, 664006777607640, 2980009468608277⟩

def sourceCPotential : Potential :=
  ⟨838681789895, 41479411858231, 186222646970525⟩

def split500Potential : Potential :=
  ⟨585348406184, 17776332071143, 79369385793808⟩

def phase4Potential : Potential :=
  ⟨69936958053, 3467956396795, 15872254270504⟩

def initialAPotential : Potential :=
  ⟨5303387732, 5106958613906, 23980501524490⟩

/-- Linear majorant for the initial-A helper on the full viable complementary
box `(total,middle,slope) ≤ (6676,153,34)`.  Unlike `initialAPotential`, its
agreement coefficients allow the left middle/slope to exceed `(135,29)`. -/
def initialAWidePotential : Potential :=
  ⟨6121183939, 5551041767050, 25579200875807⟩

def sourceR1200 : SourceNumbers :=
  ⟨328400, 6641, 1480, 5090867013182078230⟩

def sourceC : SourceNumbers :=
  ⟨82100, 1660, 370, 18278038734560710⟩

def sourceSplit500 : SourceNumbers :=
  ⟨42000, 1383, 310, 4003459072456058⟩

def sourcePhase4 : SourceNumbers :=
  ⟨24000, 484, 106, 92137303795050⟩

structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 29 → middle p ≤ 135 → total p ≤ 6676 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

theorem source_gaps_exact :
    [sourceR1200.gap, sourceC.gap, sourceSplit500.gap, sourcePhase4.gap] =
      [5090867013182078230, 18278038734560710,
        4003459072456058, 92137303795050] := by
  rfl

end ProximityPrize.SubmissionLower.LocatorPhase6803Oracle
