import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck11
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData15
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData14
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData16

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck15

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 15 LocatorPhase6803ReceiptRowData15.base LocatorPhase6803ReceiptRowData15.threshold LocatorPhase6803ReceiptRowData15.prefixData
      (LocatorPhase6803ReceiptRowData14.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 15 LocatorPhase6803ReceiptRowData15.prefixData (LocatorPhase6803ReceiptRowData16.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck15
