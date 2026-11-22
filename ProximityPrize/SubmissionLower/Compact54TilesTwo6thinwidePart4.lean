import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top10
private abbrev P := PaidBatch .two6thinwide 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [56795953193,22503338045,22201334035,17688269075,13376791827,8830170423,4501651767,89309547]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [55756139,173127027,156416371,106085747,5424504,5424508,22200704,22200708]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4484867467,173125003,122794379,22200712,8947601807,4585528719,38976908,38976912]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [38976916,55753112,22197663,55753116,55753120,72529316,22196651,72529320]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [72529324,89305520,5352884,89305524,89236923,38906299,5352888,89305528]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [5352892,89305532,13158480323,8830093763,106081728,5351876,106081732,5351880]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081736,5351884,106081740,22128080,106081744,106012119,38904279,22128084]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106081748,22128088,106081752,22128092,106081756,38904288,106081760,122787303]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122788327,22127076,122857956,22127080,122857960,22127084,122857964,38903280]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857968,38903284,122857972,38903288,122857976,8612055551,38903292,122857980]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [38903296,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 128 30 8 = true := by decide +kernel
private theorem i38 : checks ts 128 38 8 = true := by decide +kernel
private theorem i46 : checks ts 128 46 4 = true := by decide +kernel
private theorem rows : checks ts 128 30 20 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 12 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6thinwide 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [69462754349,22251668707,26211163361,13309491425,4501649739,4400988489,9048268111,8880499023]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [324121935,106086759,55756133,5424500,5424504,106084735,55754111,5424508]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22200704,22200708,22200712,38976908,38976912,189901207,139570583,72462743]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [38976916,55753112,13225723295,4669412767,22197663,55753116,55753120,72529316]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22196651,72529320,72529324,89305520,89305524,5352888,89305528,223452607]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [156344767,89236927,5352892,89305532,106081728,5351876,106081732,5351880]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081736,5351884,106081740,5351888,106081744,22128084,106081748,22128088]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106081752,22128092,106081756,22128096,106081760,22127076,122857956,22127080]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857960,22127084,122857964,8662386163,4367421939,22127088,122857968,38903284]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857972,38902267,38903288,122857976,38903292,122857980,38903296,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 128 33 8 = true := by decide +kernel
private theorem i41 : checks ts 128 41 8 = true := by decide +kernel
private theorem i49 : checks ts 128 49 1 = true := by decide +kernel
private theorem rows : checks ts 128 33 17 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 13 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

end Compact50PriceTableTwo6thinwide
