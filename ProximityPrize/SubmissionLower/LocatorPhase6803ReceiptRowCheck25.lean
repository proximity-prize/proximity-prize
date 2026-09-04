import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck21
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData25
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData24
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData26

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck25

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 25 LocatorPhase6803ReceiptRowData25.base LocatorPhase6803ReceiptRowData25.threshold LocatorPhase6803ReceiptRowData25.prefixData
      (LocatorPhase6803ReceiptRowData24.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 25 LocatorPhase6803ReceiptRowData25.prefixData (LocatorPhase6803ReceiptRowData26.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck25
