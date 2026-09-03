import ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked
import ProximityPrize.SubmissionLower.LocatorPhase6800FastChannelCount
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData08

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData08.threshold 8 120 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 120,
    ThresholdAtOf LocatorPhase6800ReceiptRowData08.threshold 8 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR08Checked
