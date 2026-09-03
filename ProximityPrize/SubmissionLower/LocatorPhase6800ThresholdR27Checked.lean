import ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR15Checked
import ProximityPrize.SubmissionLower.LocatorPhase6800FastChannelCount
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData27

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData27.threshold 27 101 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 101,
    ThresholdAtOf LocatorPhase6800ReceiptRowData27.threshold 27 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR27Checked
