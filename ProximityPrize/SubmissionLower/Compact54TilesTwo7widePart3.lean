import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top8
private abbrev P := PaidBatch .two7wide 8
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [39751475235,52419528755,5493668931,22103165191,17623654663,4789089543,22303891755,13731002667]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [125091171,74760547,4587757939,4503939443,208974195,7651700,7651704,108311935]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [57981311,7651708,24427904,24427908,24427912,41204108,41204112,41204116]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [57980312,8966605215,4604532127,292789663,57980316,57980320,108308903,41201063]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [74756516,74756520,74756524,91532720,91532724,141861307,91530683,91532728]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91532732,108308928,108308932,108308936,108308940,125085136,125085140,125085144]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [141861340,141861344,24419815,141861348,57906667,57973227,141861352,158637548]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [25794077171,158637552,8597503479,158637556]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 125 24 8 = true := by decide +kernel
private theorem i32 : checks ts 125 32 8 = true := by decide +kernel
private theorem i40 : checks ts 125 40 8 = true := by decide +kernel
private theorem i48 : checks ts 125 48 1 = true := by decide +kernel
private theorem rows : checks ts 125 24 25 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 10 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two7wide 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [39650815015,48091010103,21985727747,13311913219,4705205507,22270471447,13764822295,108313959]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [57983335,4503940459,4403279211,7651700,7651704,8916276607,4587823487,292858239]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [7651708,24427904,74757511,24426887,24427908,24427912,41204108,41204112]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [41204116,57980312,91532703,41202079,57980316,57980320,57980324,74756520]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [74756524,74756528,91532724,91532728,91532732,91532736,125084103,57976263]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [108308932,108308936,4419982799,158637519,108308940,108308944,21616553431,125085140]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [125085144,125085148,125085152,141861348,8647837163,4352872939,141861352,41196015]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [141861356,141861360,158637556]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 125 27 8 = true := by decide +kernel
private theorem i35 : checks ts 125 35 8 = true := by decide +kernel
private theorem i43 : checks ts 125 43 6 = true := by decide +kernel
private theorem rows : checks ts 125 27 22 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 11 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

end Compact50PriceTableTwo7wide
