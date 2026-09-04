import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck06
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData10
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData09
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData11

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck10

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 10 LocatorPhase6803ReceiptRowData10.base LocatorPhase6803ReceiptRowData10.threshold LocatorPhase6803ReceiptRowData10.prefixData
      (LocatorPhase6803ReceiptRowData09.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 10 LocatorPhase6803ReceiptRowData10.prefixData (LocatorPhase6803ReceiptRowData11.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck10
