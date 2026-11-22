import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top9
private abbrev P := PaidBatch .two6wider 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [52283796519,39719510075,22286855387,26465109211,17556873531,13161248059,377079099,4453938559]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4386831743,17556800899,8950159747,4520977815,4453936535,58310039,24756631,7980436]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [7980440,21734256031,24756636,24756640,91862439,41531815,41532836,41532840]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [41532844,58309040,58309044,58309048,75083199,24752575,75085244,75085248]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91861444,91861448,58303951,58304975,91861452,108637648,108637652,4302871003]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [7971291,108637656]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 118 27 8 = true := by decide +kernel
private theorem i35 : checks ts 118 35 8 = true := by decide +kernel
private theorem i43 : checks ts 118 43 7 = true := by decide +kernel
private theorem rows : checks ts 118 27 23 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 11 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6wider 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [43744196651,35474875451,26565769451,18009789675,13228353863,13110982983,4437162367,142197119]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91866495,7980436,4504267163,4403605915,7980440,7980444,75086243,24755619]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [24756640,24756644,21684058539,13094130091,41532840,41532844,4470645171,41532848]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91861431,41530807,58309044,58309048,58309052,75085248,75085252,75085256]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [58304975,41528783,91861452,91861456,91861460,108637656]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 118 30 8 = true := by decide +kernel
private theorem i38 : checks ts 118 38 8 = true := by decide +kernel
private theorem i46 : checks ts 118 46 4 = true := by decide +kernel
private theorem rows : checks ts 118 30 20 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 12 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6wider 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [47921726511,18429228095,26548995283,17993015507,8782460267,4453941611,21767947663,8899829135]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [75088275,24757651,4537821591,4437160343,125417883,75087259,7980440,7980444]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [7980448,24756644,24756648,41532844,41532848,41532852,91861435,41530811]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [58309048,58309052,58309056,75085252,75085256,75085260,41527763,41528787]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91861456,17204544983,8614615511,91861460,7972315,91861464]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 118 33 8 = true := by decide +kernel
private theorem i41 : checks ts 118 41 8 = true := by decide +kernel
private theorem i49 : checks ts 118 49 1 = true := by decide +kernel
private theorem rows : checks ts 118 33 17 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 13 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two6wider 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [56798711859,22120272155,17657538843,9050897691,158973323,108642699,75089291,4571310479]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [4487491983,192526735,7980444,7980448,24756644,24756648,24756652,41532848]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [13043798455,4453867959,41532852,41532856,91861439,41530815,58309052,58309056]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [58309060,75085256,75085260,41527763,41528787,75085264,91861460,91861464]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 118 36 8 = true := by decide +kernel
private theorem i44 : checks ts 118 44 6 = true := by decide +kernel
private theorem rows : checks ts 118 36 14 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 14 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6wider
