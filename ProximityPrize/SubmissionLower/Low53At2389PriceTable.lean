import ProximityPrize.SubmissionLower.Low53At2389PriceTableEmpty
import ProximityPrize.SubmissionLower.Low53At2389PriceTableOne3
import ProximityPrize.SubmissionLower.Low53At2389PriceTableOne4
import ProximityPrize.SubmissionLower.Low53At2389PriceTableOne5
import ProximityPrize.SubmissionLower.Low53At2389PriceTableOne6
import ProximityPrize.SubmissionLower.Low53At2389PriceTableOne7
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand6
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand7
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand8
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand9
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand10
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand11
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand12
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand13
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand14
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand15
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand16
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand17
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand18
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand19
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand20
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand21
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand22
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand23
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand24
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand25
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand26
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand27
import ProximityPrize.SubmissionLower.Low53At2389PriceTableTwoBand28

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTable
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

theorem price (top : ℕ) (htop : top ≤ 13) (k : Band) (a : Shape) (ha : Valid a)
    (hc : InBox ((start k).plus a) (fullCap top)) : Covered top k a := by
  cases k with
  | empty => exact Low53At2389PriceTableEmpty.price top htop a ha hc
  | one3 => exact Low53At2389PriceTableOne3.price top htop a ha hc
  | one4 => exact Low53At2389PriceTableOne4.price top htop a ha hc
  | one5 => exact Low53At2389PriceTableOne5.price top htop a ha hc
  | one6 => exact Low53At2389PriceTableOne6.price top htop a ha hc
  | one7 => exact Low53At2389PriceTableOne7.price top htop a ha hc
  | two6 w =>
    fin_cases w
    · exact Low53At2389PriceTableTwoBand6.Band6.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand7.Band7.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand8.Band8.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand9.Band9.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand10.Band10.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand11.Band11.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand12.Band12.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand13.Band13.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand14.Band14.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand15.Band15.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand16.Band16.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand17.Band17.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand18.Band18.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand19.Band19.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand20.Band20.price top htop a ha hc
  | two7 w =>
    fin_cases w
    · exact Low53At2389PriceTableTwoBand21.Band21.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand22.Band22.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand23.Band23.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand24.Band24.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand25.Band25.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand26.Band26.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand27.Band27.price top htop a ha hc
    · exact Low53At2389PriceTableTwoBand28.Band28.price top htop a ha hc

#print axioms price

end Low53At2389PriceTable
