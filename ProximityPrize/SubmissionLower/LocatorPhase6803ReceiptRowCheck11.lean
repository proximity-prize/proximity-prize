import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck07
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData11
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData10
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData12

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck11

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 11 LocatorPhase6803ReceiptRowData11.base LocatorPhase6803ReceiptRowData11.threshold LocatorPhase6803ReceiptRowData11.prefixData
      (LocatorPhase6803ReceiptRowData10.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 11 LocatorPhase6803ReceiptRowData11.prefixData (LocatorPhase6803ReceiptRowData12.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck11
