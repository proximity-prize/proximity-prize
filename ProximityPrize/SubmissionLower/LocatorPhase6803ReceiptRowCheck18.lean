import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck14
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData18
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData17
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData19

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck18

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 18 LocatorPhase6803ReceiptRowData18.base LocatorPhase6803ReceiptRowData18.threshold LocatorPhase6803ReceiptRowData18.prefixData
      (LocatorPhase6803ReceiptRowData17.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 18 LocatorPhase6803ReceiptRowData18.prefixData (LocatorPhase6803ReceiptRowData19.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck18
