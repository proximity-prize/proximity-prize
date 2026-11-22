import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .empty 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [2197883909,704712713,4496364553,4412480525,17549370381,51909638165,60684921893,100736045]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [251797549,56625965113,402723901,167843901,688069705,1191385193,18455995497,1325801581]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22096656497,26408865905,10049885345,39277915309,26443682989,10049884341,34681499897,9314424057]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [26761246985,26795595021,22098112837,17719527749,17451364681,13072516425,17535114577,4432250233]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4398763385,8794321293,4432248205,70241685,36688277,47732762013,4365206941,3133857]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [3133861,8911691177,4583238057,19910057,3133864,4348433833,3136937,420815277]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [3133868,3136940,103726513,103793073,53462449,19909041,19910064,3136944]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [19910068,3136948,3131833,19910072,36689337,19913144,36686268,19913148]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4415467969,103725505,19908033,36686272,19913152,87017924,17484843465,103794120]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [53460429,19907021,103794124,103794128,3129813,103794132,120570328,21695853021]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [70236637,19906013,120570332,120500705,53392865,120570336,137346532,137346536]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [137346540,4398688753,53458417,3127793,137346544,3127797,137346548,8693652985]) (by decide +kernel)]
private def p2 : List P := [Compact54FastPrice.fastBatch (unpack [154122744,154122748,68492801,70234625,19904001,154122752,25822844421,137345540]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [3202564,3126793,137345544,3202568,4314802701,154121740,3202572,154121744]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [3202576]) (by decide +kernel)]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 132 3 8 = true := by decide +kernel
private theorem i11 : checks ts 132 11 8 = true := by decide +kernel
private theorem i19 : checks ts 132 19 8 = true := by decide +kernel
private theorem i27 : checks ts 132 27 8 = true := by decide +kernel
private theorem i35 : checks ts 132 35 8 = true := by decide +kernel
private theorem i43 : checks ts 132 43 8 = true := by decide +kernel
private theorem i51 : checks ts 132 51 5 = true := by decide +kernel
private theorem rows : checks ts 132 3 53 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51)))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤132) (hj : a.j≤55) :
    Covered 1 .empty a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

end Compact50PriceTableEmpty
