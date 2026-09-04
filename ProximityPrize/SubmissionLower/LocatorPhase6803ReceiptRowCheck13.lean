import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck09
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData13
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData12
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData14

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck13

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 13 LocatorPhase6803ReceiptRowData13.base LocatorPhase6803ReceiptRowData13.threshold LocatorPhase6803ReceiptRowData13.prefixData
      (LocatorPhase6803ReceiptRowData12.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 13 LocatorPhase6803ReceiptRowData13.prefixData (LocatorPhase6803ReceiptRowData14.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck13
