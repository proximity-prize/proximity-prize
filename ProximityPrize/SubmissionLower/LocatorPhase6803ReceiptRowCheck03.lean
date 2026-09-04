import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData03
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData02
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData04

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck03

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 3 LocatorPhase6803ReceiptRowData03.base LocatorPhase6803ReceiptRowData03.threshold LocatorPhase6803ReceiptRowData03.prefixData
      (LocatorPhase6803ReceiptRowData02.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 3 LocatorPhase6803ReceiptRowData03.prefixData (LocatorPhase6803ReceiptRowData04.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck03
