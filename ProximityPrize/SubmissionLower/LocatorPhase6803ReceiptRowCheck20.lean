import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck16
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData20
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData19
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData21

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck20

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 20 LocatorPhase6803ReceiptRowData20.base LocatorPhase6803ReceiptRowData20.threshold LocatorPhase6803ReceiptRowData20.prefixData
      (LocatorPhase6803ReceiptRowData19.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 20 LocatorPhase6803ReceiptRowData20.prefixData (LocatorPhase6803ReceiptRowData21.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck20
