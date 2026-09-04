import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck10
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData14
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData13
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData15

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck14

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 14 LocatorPhase6803ReceiptRowData14.base LocatorPhase6803ReceiptRowData14.threshold LocatorPhase6803ReceiptRowData14.prefixData
      (LocatorPhase6803ReceiptRowData13.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 14 LocatorPhase6803ReceiptRowData14.prefixData (LocatorPhase6803ReceiptRowData15.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck14
