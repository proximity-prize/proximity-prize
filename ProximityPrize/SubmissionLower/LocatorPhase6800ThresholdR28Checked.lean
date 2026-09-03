import ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR16Checked
import ProximityPrize.SubmissionLower.LocatorPhase6800FastChannelCount
import ProximityPrize.SubmissionLower.LocatorPhase6800ReceiptRowData28

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked

open LocatorPhase6800Oracle LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem checkedFast : FastThresholdRIndexedOf LocatorPhase6800ReceiptRowData28.threshold 28 100 := by
  decide +kernel

theorem checked : ∀ V ∈ List.range 100,
    ThresholdAtOf LocatorPhase6800ReceiptRowData28.threshold 28 V := by
  intro V hV
  exact fastThresholdAtOf_sound _ _ _ (checkedFast V hV)

#print axioms checked

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdR28Checked
