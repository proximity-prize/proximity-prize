import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty
import ProximityPrize.SubmissionLower.Compact50PriceTableOne3
import ProximityPrize.SubmissionLower.Compact50PriceTableOne3wide
import ProximityPrize.SubmissionLower.Compact50PriceTableOne4
import ProximityPrize.SubmissionLower.Compact50PriceTableOne5
import ProximityPrize.SubmissionLower.Compact50PriceTableOne6
import ProximityPrize.SubmissionLower.Compact50PriceTableOne7
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6thin
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6thinwide
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6wide
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6wider
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo7
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo7wide

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTable
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)

theorem price (top : ℕ) (htop : top ≤ 14) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (fullCap top)) : Covered top k a := by
  cases k with
  | empty => exact Compact50PriceTableEmpty.price top htop a ha hc
  | one3 => exact Compact50PriceTableOne3.price top htop a ha hc
  | one3wide => exact Compact50PriceTableOne3wide.price top htop a ha hc
  | one4 => exact Compact50PriceTableOne4.price top htop a ha hc
  | one5 => exact Compact50PriceTableOne5.price top htop a ha hc
  | one6 => exact Compact50PriceTableOne6.price top htop a ha hc
  | one7 => exact Compact50PriceTableOne7.price top htop a ha hc
  | two6thin => exact Compact50PriceTableTwo6thin.price top htop a ha hc
  | two6thinwide => exact Compact50PriceTableTwo6thinwide.price top htop a ha hc
  | two6wide => exact Compact50PriceTableTwo6wide.price top htop a ha hc
  | two6wider => exact Compact50PriceTableTwo6wider.price top htop a ha hc
  | two7 => exact Compact50PriceTableTwo7.price top htop a ha hc
  | two7wide => exact Compact50PriceTableTwo7wide.price top htop a ha hc

#print axioms price
end Compact50PriceTable
