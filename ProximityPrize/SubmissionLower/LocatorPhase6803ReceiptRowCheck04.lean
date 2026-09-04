import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData04
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData03
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData05

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck04

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 4 LocatorPhase6803ReceiptRowData04.base LocatorPhase6803ReceiptRowData04.threshold LocatorPhase6803ReceiptRowData04.prefixData
      (LocatorPhase6803ReceiptRowData03.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 4 LocatorPhase6803ReceiptRowData04.prefixData (LocatorPhase6803ReceiptRowData05.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck04
