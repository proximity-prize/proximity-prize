import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck20
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData24
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData23
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData25

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck24

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 24 LocatorPhase6803ReceiptRowData24.base LocatorPhase6803ReceiptRowData24.threshold LocatorPhase6803ReceiptRowData24.prefixData
      (LocatorPhase6803ReceiptRowData23.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 24 LocatorPhase6803ReceiptRowData24.prefixData (LocatorPhase6803ReceiptRowData25.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck24
