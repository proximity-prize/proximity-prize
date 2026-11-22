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

namespace Top4
private abbrev P := PaidBatch .two6thinwide 4
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [31897301011,52466176029,69596972079,18039329023,26579920127,26412417279,30439021827,9064856835]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [13242572127,13108358495,4451384695,156419447,4434537879,4384273815,13292831131,8930824603]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [55754143,22200735,5424540,5424544,22200740,22200744,72529327,22198703]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [38976940,38976944,4468088247,4384204215,55753140,72461755,55751099,55753144]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [55753148,21714724291,13158612419,72529344,72529348,34599547339,89305544,25992844751]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [72459727,22129103,22195663,89305548,89305552,5351892,106081748,5351896]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081752,5351900,106081756,89234915,38904291,22128096,106081760,5350884]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857956,5350888,122857960,4384199151,89233903,22127084,122857964,22127088]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857968,22127092,122857972,38903288,122857976,8611983869,22121981,38903292]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857980,38903296,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 128 12 8 = true := by decide +kernel
private theorem i20 : checks ts 128 20 8 = true := by decide +kernel
private theorem i28 : checks ts 128 28 8 = true := by decide +kernel
private theorem i36 : checks ts 128 36 8 = true := by decide +kernel
private theorem i44 : checks ts 128 44 6 = true := by decide +kernel
private theorem rows : checks ts 128 12 38 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 6 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6thinwide 5
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [35839949847,65132978209,39649648697,26814800079,30808046799,17923218639,17470435627,408012075]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4501647731,4451383667,156418419,30639865211,22050200955,13359807875,8947404163,8830032259]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [8763057539,5424527,5424528,5424532,72530331,38976923,22200728,22200732]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22200736,106082727,55752103,38976932,38976936,173122991,122792367,89238959]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [55753132,55753136,72529332,72529336,4451310015,156344767,72529340,89305536]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [5418439,89305540,13125055947,106081736,5351884,106081740,5351888,106081744]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [5351892,106081748,4468084187,173118939,22128088,106081752,22128092,106081756]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22128096,106081760,106011111,55680487,22127076,122857956,22127080,122857960]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22127084,122857964,22127088,122857968,4350641653,38903284,122857972,38903288]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857976,38903292,122857980,55679488,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 128 15 8 = true := by decide +kernel
private theorem i23 : checks ts 128 23 8 = true := by decide +kernel
private theorem i31 : checks ts 128 31 8 = true := by decide +kernel
private theorem i39 : checks ts 128 39 8 = true := by decide +kernel
private theorem i47 : checks ts 128 47 3 = true := by decide +kernel
private theorem rows : checks ts 128 15 35 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 7 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

end Compact50PriceTableTwo6thinwide
