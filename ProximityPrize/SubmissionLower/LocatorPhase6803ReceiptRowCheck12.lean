import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck08
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData12
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData11
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData13

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck12

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 12 LocatorPhase6803ReceiptRowData12.base LocatorPhase6803ReceiptRowData12.threshold LocatorPhase6803ReceiptRowData12.prefixData
      (LocatorPhase6803ReceiptRowData11.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 12 LocatorPhase6803ReceiptRowData12.prefixData (LocatorPhase6803ReceiptRowData13.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck12
