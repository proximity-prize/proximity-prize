import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty
import ProximityPrize.SubmissionLower.Compact50PriceTableOne
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTable

theorem price (top : ℕ) (htop : top ≤ 13) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (fullCap top)) : Covered top k a := by
  cases k
  · exact Compact50PriceTableEmpty.price top htop a ha hc
  · exact Compact50PriceTableOne.price top htop a ha hc
  · exact Compact50PriceTableTwo.price top htop a ha hc

#print axioms price
end Compact50PriceTable
