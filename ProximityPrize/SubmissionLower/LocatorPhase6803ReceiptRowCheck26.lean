import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck22
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData26
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData25
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData27

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck26

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 26 LocatorPhase6803ReceiptRowData26.base LocatorPhase6803ReceiptRowData26.threshold LocatorPhase6803ReceiptRowData26.prefixData
      (LocatorPhase6803ReceiptRowData25.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 26 LocatorPhase6803ReceiptRowData26.prefixData (LocatorPhase6803ReceiptRowData27.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck26
