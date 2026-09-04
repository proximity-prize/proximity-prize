import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck01
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData05
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData04
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData06

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck05

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 5 LocatorPhase6803ReceiptRowData05.base LocatorPhase6803ReceiptRowData05.threshold LocatorPhase6803ReceiptRowData05.prefixData
      (LocatorPhase6803ReceiptRowData04.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 5 LocatorPhase6803ReceiptRowData05.prefixData (LocatorPhase6803ReceiptRowData06.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck05
