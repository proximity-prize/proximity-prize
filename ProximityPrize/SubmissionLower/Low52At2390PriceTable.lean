import ProximityPrize.SubmissionLower.Low52At2390PriceTableEmpty
import ProximityPrize.SubmissionLower.Low52At2390PriceTableOne3
import ProximityPrize.SubmissionLower.Low52At2390PriceTableOne4
import ProximityPrize.SubmissionLower.Low52At2390PriceTableOne5
import ProximityPrize.SubmissionLower.Low52At2390PriceTableOne6
import ProximityPrize.SubmissionLower.Low52At2390PriceTableOne7
import ProximityPrize.SubmissionLower.Low52At2390PriceTableTwo6A
import ProximityPrize.SubmissionLower.Low52At2390PriceTableTwo6B
import ProximityPrize.SubmissionLower.Low52At2390PriceTableTwo6C
import ProximityPrize.SubmissionLower.Low52At2390PriceTableTwo7A
import ProximityPrize.SubmissionLower.Low52At2390PriceTableTwo7B

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTable
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

theorem price (top : ℕ) (htop : top ≤ 13) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (fullCap top)) : Covered top k a := by
  cases k with
  | empty => exact Low52At2390PriceTableEmpty.price top htop a ha hc
  | one3 => exact Low52At2390PriceTableOne3.price top htop a ha hc
  | one4 => exact Low52At2390PriceTableOne4.price top htop a ha hc
  | one5 => exact Low52At2390PriceTableOne5.price top htop a ha hc
  | one6 => exact Low52At2390PriceTableOne6.price top htop a ha hc
  | one7 => exact Low52At2390PriceTableOne7.price top htop a ha hc
  | two6 w =>
    fin_cases w
    · exact Low52At2390PriceTableTwo6A.Band6.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6A.Band7.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6A.Band8.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6A.Band9.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6A.Band10.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6B.Band11.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6B.Band12.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6B.Band13.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6B.Band14.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6B.Band15.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6C.Band16.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6C.Band17.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6C.Band18.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6C.Band19.price top htop a ha hc
    · exact Low52At2390PriceTableTwo6C.Band20.price top htop a ha hc
  | two7 w =>
    fin_cases w
    · exact Low52At2390PriceTableTwo7A.Band21.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7A.Band22.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7A.Band23.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7A.Band24.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7B.Band25.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7B.Band26.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7B.Band27.price top htop a ha hc
    · exact Low52At2390PriceTableTwo7B.Band28.price top htop a ha hc

#print axioms price

end Low52At2390PriceTable
