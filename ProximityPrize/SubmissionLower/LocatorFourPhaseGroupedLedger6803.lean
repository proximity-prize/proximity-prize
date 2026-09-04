import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeLedger6803
import ProximityPrize.SubmissionLower.LocatorR1200Source6803
import ProximityPrize.SubmissionLower.LocatorPhase4Source6803

/-!
# Four-phase arithmetic handoff for the grouped 68.03 chain

The grouped-chain geometry does not require all eight sources recorded in
`LocatorGroupedDerivativeLedger6803`.  Re-running the exact breakpoint scan
with the first three 68.03 profiles and the retuned `m = 350` fourth profile
gives the joint maximum below.  Adding the same deliberately conservative
proper-predecessor exceptional budget still leaves nearly `4.79e14` points
of slack.

This is an arithmetic connector, not a replacement for a checked phase
receipt: the value `retunedFourJointMaximum` must be supplied by regenerated
6803 prefix tables before it can be used in the final cardinality theorem.
-/

namespace ProximityPrize.SubmissionLower.LocatorFourPhaseGroupedLedger6803

open LocatorGroupedDerivativeLedger6803

set_option autoImplicit false

/-- Exhaustive joint maximum of the grouped one-charge model for the four
sources `(4800,1200,1000,350)`.  The maximizing raw state is
`(R,V,Z) = (17,42,6523)`. -/
def retunedFourJointMaximum : ℕ := 274502008609551624

def regularAtWitness : ℕ := 273609253427606378

def mainGroupedAtWitness : ℕ := 26114287642879

def mainTailAtWitness : ℕ := 1842631354450

/-- Initial-factor potential at the complementary raw state `(16,78,0)`. -/
def complementPotentialAtWitness : ℕ := 864240652545812

def complementGroupedAtWitness : ℕ := 557610402105

theorem retunedFourJointMaximum_decomposition :
    retunedFourJointMaximum =
      regularAtWitness + mainGroupedAtWitness + mainTailAtWitness +
        complementPotentialAtWitness + complementGroupedAtWitness := by
  native_decide

/-- The four-phase maximum plus the already checked exceptional-cut budget. -/
def retunedFourConservativeTotal : ℕ :=
  retunedFourJointMaximum + properExceptionalCap

theorem retunedFourConservativeTotal_exact :
    retunedFourConservativeTotal = 274502025217677576 := by
  rw [retunedFourConservativeTotal, properExceptionalCap_exact]
  native_decide

theorem retunedFourConservativeTotal_lt_budget :
    retunedFourConservativeTotal < budget := by
  rw [retunedFourConservativeTotal_exact]
  native_decide

theorem retunedFourSlack_exact :
    budget - retunedFourConservativeTotal = 478697888551439 := by
  rw [retunedFourConservativeTotal_exact]
  native_decide

/-- The five extra phases improve the cap, but are not logically needed to
cross the 68.03 budget. -/
theorem eightPhase_refines_retunedFour :
    conservativeTotal ≤ retunedFourConservativeTotal := by
  rw [conservativeTotal_exact, retunedFourConservativeTotal_exact]
  native_decide

/-- Final arithmetic handoff for a regenerated four-phase receipt. -/
theorem closes_retuned_four_phase_target {actual : ℕ}
    (hactual : actual ≤ retunedFourConservativeTotal) : actual < budget :=
  hactual.trans_lt retunedFourConservativeTotal_lt_budget

end ProximityPrize.SubmissionLower.LocatorFourPhaseGroupedLedger6803
