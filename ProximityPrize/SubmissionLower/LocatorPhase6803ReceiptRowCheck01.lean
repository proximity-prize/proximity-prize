import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData01
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData02

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck01

open LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stateChecked :
    RowValid 1 LocatorPhase6803ReceiptRowData01.base LocatorPhase6803ReceiptRowData01.threshold LocatorPhase6803ReceiptRowData01.prefixData
      (fun _ => zeroPrefix) := by
  native_decide

theorem prefixChecked :
    PrefixRowValid 1 LocatorPhase6803ReceiptRowData01.prefixData (LocatorPhase6803ReceiptRowData02.prefixData) := by
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowCheck01
