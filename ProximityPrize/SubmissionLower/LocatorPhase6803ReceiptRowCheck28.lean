import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck24
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData28
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData27
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData29

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck28

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 28 LocatorPhase6803ReceiptRowData28.base LocatorPhase6803ReceiptRowData28.threshold LocatorPhase6803ReceiptRowData28.prefixData
      (LocatorPhase6803ReceiptRowData27.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 28 LocatorPhase6803ReceiptRowData28.prefixData (LocatorPhase6803ReceiptRowData29.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck28
