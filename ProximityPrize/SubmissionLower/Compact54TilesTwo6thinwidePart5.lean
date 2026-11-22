import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

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

namespace Top12
private abbrev P := PaidBatch .two6thinwide 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [56644964401,22016790775,21815535861,4702781685,8897276235,4551980363,4451319113,89245017]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106085747,55755123,5424497,5424500,8947405179,8863718779,5424504,5424508]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22200704,22200708,106083723,55753099,22200712,38976908,38976912,206678423]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [139570583,89239959,38976916,55753112,55753116,55753120,72529316,72529320]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22196655,72529324,72529328,89305524,5352888,89305528,240229823,173121983]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106014143,5352892,89305532,106081728,106081732,5351880,106081736,5351884]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081740,4501639635,206674387,5351888,106081744,5351892,106081748,22128088]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106081752,22128092,106081756,22128096,106081760,5350884,122857956,22127080]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857960,22127084,122857964,22127088,122857968,22127092,122857972,38903288]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857976,38903292,122857980,38903296,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 128 36 8 = true := by decide +kernel
private theorem i44 : checks ts 128 44 6 = true := by decide +kernel
private theorem rows : checks ts 128 36 14 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 14 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6thinwide
