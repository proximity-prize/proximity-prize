import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck03
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData07
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData06
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData08

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck07

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 7 LocatorPhase6803ReceiptRowData07.base LocatorPhase6803ReceiptRowData07.threshold LocatorPhase6803ReceiptRowData07.prefixData
      (LocatorPhase6803ReceiptRowData06.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 7 LocatorPhase6803ReceiptRowData07.prefixData (LocatorPhase6803ReceiptRowData08.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck07
