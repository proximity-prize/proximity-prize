import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty
import ProximityPrize.SubmissionLower.Compact50PriceTableOne3
import ProximityPrize.SubmissionLower.Compact50PriceTableOne4
import ProximityPrize.SubmissionLower.Compact50PriceTableOne5
import ProximityPrize.SubmissionLower.Compact50PriceTableOne6
import ProximityPrize.SubmissionLower.Compact50PriceTableOne7
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6thin
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6wide
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo7

set_option Elab.async false
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
  cases k
  · exact Compact50PriceTableEmpty.price top htop a ha hc
  · exact Compact50PriceTableOne3.price top htop a ha hc
  · exact Compact50PriceTableOne4.price top htop a ha hc
  · exact Compact50PriceTableOne5.price top htop a ha hc
  · exact Compact50PriceTableOne6.price top htop a ha hc
  · exact Compact50PriceTableOne7.price top htop a ha hc
  · exact Compact50PriceTableTwo6thin.price top htop a ha hc
  · exact Compact50PriceTableTwo6wide.price top htop a ha hc
  · exact Compact50PriceTableTwo7.price top htop a ha hc

#print axioms price
end Compact50PriceTable
