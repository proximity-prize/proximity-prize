import ProximityPrize.SubmissionLower.LocatorFourPhaseGroupedLedger6803

/-!
# Coarse grouped-charge handoff for a four-phase 68.03 receipt

The tight grouped ledger couples the two one-step incidence charges and the
`R`-free tail to the raw state optimized by the phase receipt.  That coupling
is not needed to close the 68.03 budget.  Monotonicity in the cumulative
degree boxes gives the three uniform envelopes recorded here; even charging
all three independently at their worst corners leaves more than `2.64e14`
points of slack.

Consequently the generated numerical receipt only has to certify the ordinary
four-phase joint bound

    phaseCap p + initialAComplement p <= receiptJointCap.

The grouped geometric bridge may then add the three uniform charges below and
the already banked proper-predecessor exceptional budget.
-/

namespace ProximityPrize.SubmissionLower.LocatorFourPhaseCoarseGroupedLedger6803

open RCN260 RCN318
open LocatorGroupedDerivativeLedger6803

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Target joint bound for the regenerated ordinary four-phase receipt. -/
def receiptJointCap : ℕ := 274473494080152190

/-- The MCA allowance after reserving the retuned 68.03 scalar list budget. -/
def protocolBudget6803 : ℕ := 274980722886578332

/-- Worst adjacent-derivative incidence box for the main regular factor:
the right flag is bounded by `(middle,slope,total) = (135,29,6676)` and the
first proper derivative drops all three positive weights by one. -/
def mainUniformStage : UnequalParameters :=
  ⟨262144, 131071, 181363, 134, 28, 6675, 135, 29, 6676⟩

/-- Worst adjacent-derivative incidence box for the complementary factor:
its wide box is `(middle,slope,total) = (153,33,6676)`. -/
def complementUniformStage : UnequalParameters :=
  ⟨262144, 131071, 181363, 152, 32, 6675, 153, 33, 6676⟩

/-- The `R`-free tail is largest before spending all but the mandatory one
unit of positive slope.  It is a residual of the *wide* middle box `153`,
hence `D = 131071 * (153 - 1)` and `L = 6676 - 1`. -/
def tailUniformStage : TightParameters :=
  ⟨262144, 131071, 181363, 131071 * 152, 6675, 1⟩

theorem mainUniformStage_exact :
    mainUniformStage.regularCountCap = 105025484947256 := by
  native_decide

theorem complementUniformStage_exact :
    complementUniformStage.regularCountCap = 135774894764398 := by
  native_decide

theorem tailUniformStage_exact :
    tailUniformStage.countCap = 2065959075425 := by
  native_decide

/-- Sum of the three deliberately independent grouped envelopes. -/
def uniformGroupedCap : ℕ :=
  mainUniformStage.regularCountCap +
    complementUniformStage.regularCountCap + tailUniformStage.countCap

theorem uniformGroupedCap_exact : uniformGroupedCap = 242866338787079 := by
  rw [uniformGroupedCap, mainUniformStage_exact,
    complementUniformStage_exact, tailUniformStage_exact]

/-- Conservative total supplied by an ordinary four-phase joint receipt,
three independent grouped envelopes, and both exceptional-cut allowances. -/
def coarseConservativeTotal : ℕ :=
  receiptJointCap + uniformGroupedCap + properExceptionalCap

theorem coarseConservativeTotal_exact :
    coarseConservativeTotal = 274716377027065221 := by
  rw [coarseConservativeTotal, uniformGroupedCap_exact,
    properExceptionalCap_exact]
  native_decide

theorem coarseConservativeTotal_lt_budget :
    coarseConservativeTotal < budget := by
  rw [coarseConservativeTotal_exact]
  native_decide

theorem coarseConservativeTotal_lt_protocolBudget6803 :
    coarseConservativeTotal < protocolBudget6803 := by
  rw [coarseConservativeTotal_exact]
  native_decide

theorem coarseSlack_exact :
    budget - coarseConservativeTotal = 264346079163794 := by
  rw [coarseConservativeTotal_exact]
  native_decide

theorem coarseProtocolSlack_exact :
    protocolBudget6803 - coarseConservativeTotal = 264345859513111 := by
  rw [coarseConservativeTotal_exact]
  native_decide

/-- Componentwise connector for the geometric assembly.  Its hypotheses
isolate the four facts that still have to come from the regenerated receipt
and the grouped-incidence bridges; no joint optimization between them is
required. -/
theorem closes_of_component_caps
    {ordinary mainCharge complementCharge tailCharge exceptionalCharge : ℕ}
    (hordinary : ordinary ≤ receiptJointCap)
    (hmain : mainCharge ≤ mainUniformStage.regularCountCap)
    (hcomplement :
      complementCharge ≤ complementUniformStage.regularCountCap)
    (htail : tailCharge ≤ tailUniformStage.countCap)
    (hexceptional : exceptionalCharge ≤ properExceptionalCap) :
    ordinary + mainCharge + complementCharge + tailCharge +
        exceptionalCharge < budget := by
  have hcoarse :
      ordinary + mainCharge + complementCharge + tailCharge +
          exceptionalCharge ≤ coarseConservativeTotal := by
    simp only [coarseConservativeTotal, uniformGroupedCap]
    omega
  exact hcoarse.trans_lt coarseConservativeTotal_lt_budget

/-- Arithmetic handoff.  The remaining geometric proof only needs to bound
the actual grouped count by this coarse total. -/
theorem closes_coarse_four_phase_target {actual : ℕ}
    (hactual : actual ≤ coarseConservativeTotal) : actual < budget :=
  hactual.trans_lt coarseConservativeTotal_lt_budget

/-- Final arithmetic handoff to the exact allowance used by
`LocatorProtocol6803`. -/
theorem closes_coarse_protocol6803_target {actual : ℕ}
    (hactual : actual ≤ coarseConservativeTotal) :
    actual < protocolBudget6803 :=
  hactual.trans_lt coarseConservativeTotal_lt_protocolBudget6803

end ProximityPrize.SubmissionLower.LocatorFourPhaseCoarseGroupedLedger6803
