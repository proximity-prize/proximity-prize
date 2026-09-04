import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck13
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData17
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData16
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData18

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck17

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 17 LocatorPhase6803ReceiptRowData17.base LocatorPhase6803ReceiptRowData17.threshold LocatorPhase6803ReceiptRowData17.prefixData
      (LocatorPhase6803ReceiptRowData16.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 17 LocatorPhase6803ReceiptRowData17.prefixData (LocatorPhase6803ReceiptRowData18.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck17
