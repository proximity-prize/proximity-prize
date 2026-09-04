import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck18
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData22
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData21
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData23

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck22

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 22 LocatorPhase6803ReceiptRowData22.base LocatorPhase6803ReceiptRowData22.threshold LocatorPhase6803ReceiptRowData22.prefixData
      (LocatorPhase6803ReceiptRowData21.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 22 LocatorPhase6803ReceiptRowData22.prefixData (LocatorPhase6803ReceiptRowData23.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck22
