import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck15
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData19
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData18
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData20

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck19

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 19 LocatorPhase6803ReceiptRowData19.base LocatorPhase6803ReceiptRowData19.threshold LocatorPhase6803ReceiptRowData19.prefixData
      (LocatorPhase6803ReceiptRowData18.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 19 LocatorPhase6803ReceiptRowData19.prefixData (LocatorPhase6803ReceiptRowData20.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck19
