import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeChain6803

/-!
# Numerical ledger for the grouped derivative-chain 68.03 target

This file banks the integer-only output of the exact phase-envelope screen.
The eight interpolation sources are listed explicitly.  The geometric target
is to group the exact derivative strata on each component of `(F, dR F)` and
charge that component once, using its first proper derivative.  At the
limiting joint state the two grouped incidence charges are the ordinary
unequal-parameter caps below.

`groupedJointMaximum` is the exhaustive maximum over the analytic phase and
activation breakpoints used by `scripts/search-locator-6803.py`; its witness
is the split

    (R,V,Z) = (18,42,5344),  complement = (15,78,1179).

The proper-predecessor exceptional cuts are charged very conservatively by
all 32 possible derivative orders in each of the fixed and residual boxes.
Thus the remaining geometric assembly may spend the corresponding two triple
mixed-volume budgets without consuming the stated final slack.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeLedger6803

open RCN095 RCN260 RCN318

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def agreements : ℕ := 181363
def budget : ℕ := 274980723106229015

/-- `(multiplicity, total cap, slope cap, middle cap, kernel gap)`. -/
abbrev PhaseSource := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The eight sources used by the grouped-chain envelope, in routing order. -/
def phaseSources : List PhaseSource :=
  [ (4800, 328400, 1480, 6641, 5090867013182078230),
    (1200, 82100, 370, 1660, 18278038734560710),
    (1000, 42000, 310, 1383, 4003459072456058),
    (350, 24000, 106, 484, 92137303795050),
    (200, 14000, 60, 276, 5661149860315),
    (170, 10200, 54, 235, 1381987576640),
    (160, 11200, 47, 221, 1140536299764),
    (140, 9800, 43, 193, 350617275723) ]

theorem phaseSources_length : phaseSources.length = 8 := by
  native_decide

/-- The first grouped incidence charge at the limiting state. -/
def mainGroupedStage : UnequalParameters :=
  ⟨n, w, agreements, 59, 17, 5403, 60, 18, 5404⟩

/-- The grouped incidence charge on the complementary factor box. -/
def complementGroupedStage : UnequalParameters :=
  ⟨n, w, agreements, 92, 14, 1271, 93, 15, 1272⟩

/-- The aggregate `R`-free tail after the main factor spends slope 18. -/
def mainTail : TightParameters :=
  ⟨n, w, agreements, w * 135, 6658, 1⟩

theorem mainGroupedStage_exact :
    mainGroupedStage.regularCountCap = 23127491868023 := by
  native_decide

theorem complementGroupedStage_exact :
    complementGroupedStage.regularCountCap = 7004080700664 := by
  native_decide

theorem mainTail_exact : mainTail.countCap = 1828708215370 := by
  native_decide

/-- Eight-phase regular envelope at the limiting state. -/
def regularAtWitness : ℕ := 273461948281345215

/-- Initial-factor potential on the complementary state `(15,78,1179)`. -/
def complementPotentialAtWitness : ℕ := 841400583155712

/-- Exact maximum of the grouped-one-charge joint model. -/
def groupedJointMaximum : ℕ := 274335309145284984

theorem groupedJointMaximum_decomposition :
    groupedJointMaximum =
      regularAtWitness + mainTail.countCap +
        mainGroupedStage.regularCountCap + complementPotentialAtWitness +
          complementGroupedStage.regularCountCap := by
  rw [mainTail_exact, mainGroupedStage_exact, complementGroupedStage_exact]
  native_decide

/-- Flags for the two possible proper-predecessor exceptional cuts. -/
def fixedFlag : FlagDegree := ⟨6259, 120, 33⟩
def residualFlag : FlagDegree := ⟨12807, 120, 33⟩

theorem fixedTripleMixed_exact :
    flagMixed fixedFlag fixedFlag fixedFlag = 171015570 := by
  native_decide

theorem residualTripleMixed_exact :
    flagMixed residualFlag residualFlag residualFlag = 347988366 := by
  native_decide

/-- Charge every possible nonterminal order in both boxes, even though a
first-proper-derivative grouping assigns each component to only one order. -/
def properExceptionalCap : ℕ :=
  32 * flagMixed fixedFlag fixedFlag fixedFlag +
    32 * flagMixed residualFlag residualFlag residualFlag

theorem properExceptionalCap_exact : properExceptionalCap = 16608125952 := by
  rw [properExceptionalCap, fixedTripleMixed_exact, residualTripleMixed_exact]

/-- Final conservative grouped-chain target, including all exceptional cuts. -/
def conservativeTotal : ℕ := groupedJointMaximum + properExceptionalCap

theorem conservativeTotal_exact :
    conservativeTotal = 274335325753410936 := by
  rw [conservativeTotal, properExceptionalCap_exact]
  native_decide

theorem conservativeTotal_lt_budget : conservativeTotal < budget := by
  rw [conservativeTotal_exact]
  native_decide

theorem conservativeSlack_exact :
    budget - conservativeTotal = 645397352818079 := by
  rw [conservativeTotal_exact]
  native_decide

/-- Arithmetic handoff: any geometric/cardinality theorem delivering the
conservative grouped cap is immediately within the 68.03 MCA budget. -/
theorem closes_grouped_target {actual : ℕ}
    (hactual : actual ≤ conservativeTotal) : actual < budget :=
  hactual.trans_lt conservativeTotal_lt_budget

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeLedger6803
