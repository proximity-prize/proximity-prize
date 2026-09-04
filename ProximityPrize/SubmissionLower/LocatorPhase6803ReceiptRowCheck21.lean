import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck17
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData21
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData20
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData22

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck21

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 21 LocatorPhase6803ReceiptRowData21.base LocatorPhase6803ReceiptRowData21.threshold LocatorPhase6803ReceiptRowData21.prefixData
      (LocatorPhase6803ReceiptRowData20.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 21 LocatorPhase6803ReceiptRowData21.prefixData (LocatorPhase6803ReceiptRowData22.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck21
