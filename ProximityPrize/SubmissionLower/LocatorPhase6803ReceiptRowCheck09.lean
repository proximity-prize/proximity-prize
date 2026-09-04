import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck05
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData09
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData08
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData10

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck09

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 9 LocatorPhase6803ReceiptRowData09.base LocatorPhase6803ReceiptRowData09.threshold LocatorPhase6803ReceiptRowData09.prefixData
      (LocatorPhase6803ReceiptRowData08.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 9 LocatorPhase6803ReceiptRowData09.prefixData (LocatorPhase6803ReceiptRowData10.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck09
