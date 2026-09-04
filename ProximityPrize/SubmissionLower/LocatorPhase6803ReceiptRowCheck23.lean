import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck19
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData23
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData22
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData24

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck23

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 23 LocatorPhase6803ReceiptRowData23.base LocatorPhase6803ReceiptRowData23.threshold LocatorPhase6803ReceiptRowData23.prefixData
      (LocatorPhase6803ReceiptRowData22.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 23 LocatorPhase6803ReceiptRowData23.prefixData (LocatorPhase6803ReceiptRowData24.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck23
