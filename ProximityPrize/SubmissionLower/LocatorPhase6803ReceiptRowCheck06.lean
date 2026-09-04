import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck02
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData06
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData05
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData07

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck06

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 6 LocatorPhase6803ReceiptRowData06.base LocatorPhase6803ReceiptRowData06.threshold LocatorPhase6803ReceiptRowData06.prefixData
      (LocatorPhase6803ReceiptRowData05.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 6 LocatorPhase6803ReceiptRowData06.prefixData (LocatorPhase6803ReceiptRowData07.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck06
