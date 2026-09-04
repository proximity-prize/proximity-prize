import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck12
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData16
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData15
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData17

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck16

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 16 LocatorPhase6803ReceiptRowData16.base LocatorPhase6803ReceiptRowData16.threshold LocatorPhase6803ReceiptRowData16.prefixData
      (LocatorPhase6803ReceiptRowData15.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 16 LocatorPhase6803ReceiptRowData16.prefixData (LocatorPhase6803ReceiptRowData17.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck16
