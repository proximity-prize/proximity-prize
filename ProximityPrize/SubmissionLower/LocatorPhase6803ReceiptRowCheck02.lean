import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData02
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData01
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData03

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck02

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 2 LocatorPhase6803ReceiptRowData02.base LocatorPhase6803ReceiptRowData02.threshold LocatorPhase6803ReceiptRowData02.prefixData
      (LocatorPhase6803ReceiptRowData01.prefixData) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 2 LocatorPhase6803ReceiptRowData02.prefixData (LocatorPhase6803ReceiptRowData03.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck02
