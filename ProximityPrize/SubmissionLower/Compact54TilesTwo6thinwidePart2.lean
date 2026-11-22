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

namespace Top6
private abbrev P := PaidBatch .two6thinwide 6
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [44077565977,60821369897,22553669693,26546369747,26395644115,9299733715,30975674667,18090846507]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [8813394243,257017155,8980959595,8930827627,4585531755,4384274811,89309563,4417761663]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22201731,5424520,13376716175,4786785679,5424524,72530323,22199699,22200720]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22200724,38976920,106082719,55752095,38976924,38976928,55753124,55753128]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [72529324,89237939,38907315,72529328,72529332,89305528,206675391,139567551]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [89236927,5352892,89305532,5418435,89305536,106081732,4451309003,5351880]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081736,5351884,106081740,5351888,106081744,22128084,106081748,22128088]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106081752,22128092,106081756,38904288,106081760,22127076,122857956,22127080]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857960,22127084,122857964,72455667,38902259,38903280,122857968,38903284]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857972,38903288,122857976,55679484,122857980,55679488,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 128 18 8 = true := by decide +kernel
private theorem i26 : checks ts 128 26 8 = true := by decide +kernel
private theorem i34 : checks ts 128 34 8 = true := by decide +kernel
private theorem i42 : checks ts 128 42 8 = true := by decide +kernel
private theorem rows : checks ts 128 18 32 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 8 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6thinwide 7
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [52432622621,65218119729,22117452019,21916197107,13275937011,26865128695,22268178679,4501649747]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4417765715,8914051423,8779836767,106086771,55756147,5424512,89307527,55754119]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [5424516,5424520,9014643087,8863716751,173125007,122794383,106083727,22200716]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [22200720,38976916,38976920,55753116,55753120,55753124,72529320,206676399]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [139568559,89237935,22196655,72529324,72529328,17486999991,8913978807,89305524]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [5352888,89305528,5352892,89305532,106081728,5351876,106081732,5351880]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [106081736,5351884,106081740,4400977363,106012115,22128080,106081744,22128084]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [106081748,22128088,106081752,22128092,106081756,38904288,106081760,22127076]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857956,22127080,122857960,89232879,55679471,38903276,122857964,38903280]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857968,55677431,38903284,122857972,38903288,122857976,25791518207,55679484]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [122857980,17185141251,55679488,122857984]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 128 21 8 = true := by decide +kernel
private theorem i29 : checks ts 128 29 8 = true := by decide +kernel
private theorem i37 : checks ts 128 37 8 = true := by decide +kernel
private theorem i45 : checks ts 128 45 5 = true := by decide +kernel
private theorem rows : checks ts 128 21 29 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 9 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

end Compact50PriceTableTwo6thinwide
