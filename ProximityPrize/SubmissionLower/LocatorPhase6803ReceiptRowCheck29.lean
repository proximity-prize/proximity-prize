import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck25
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData29
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData28

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck29

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 29 LocatorPhase6803ReceiptRowData29.base LocatorPhase6803ReceiptRowData29.threshold LocatorPhase6803ReceiptRowData29.prefixData
      (LocatorPhase6803ReceiptRowData28.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 29 LocatorPhase6803ReceiptRowData29.prefixData (fun _ => defaultPrefix) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck29
