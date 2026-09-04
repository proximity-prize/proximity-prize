import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck04
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData08
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData07
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData09

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck08

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 8 LocatorPhase6803ReceiptRowData08.base LocatorPhase6803ReceiptRowData08.threshold LocatorPhase6803ReceiptRowData08.prefixData
      (LocatorPhase6803ReceiptRowData07.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 8 LocatorPhase6803ReceiptRowData08.prefixData (LocatorPhase6803ReceiptRowData09.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck08
