import ProximityPrize.SubmissionLower.Low48PriceTableTwo

set_option Elab.async false
namespace Low48PriceTable
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low48Price (fullCap physicalPrice)
open Low48PriceCaps (Band order allowance start)

theorem price (top : ℕ) (htop : top ≤ 13) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (fullCap top)) :
    physicalPrice a (order k a) ≤ allowance top k a.j := by
  cases k
  · exact Low48PriceTableEmpty.price top htop a ha hc
  · exact Low48PriceTableOne.price top htop a ha hc
  · exact Low48PriceTableTwo.price top htop a ha hc

#print axioms price
end Low48PriceTable
