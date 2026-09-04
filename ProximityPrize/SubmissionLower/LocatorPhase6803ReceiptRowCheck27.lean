import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck23
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData27
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData26
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData28

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck27

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 27 LocatorPhase6803ReceiptRowData27.base LocatorPhase6803ReceiptRowData27.threshold LocatorPhase6803ReceiptRowData27.prefixData
      (LocatorPhase6803ReceiptRowData26.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 27 LocatorPhase6803ReceiptRowData27.prefixData (LocatorPhase6803ReceiptRowData28.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck27
