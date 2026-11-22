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

namespace Top1
private abbrev P := PaidBatch .two7wide 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [27603569671,31529445395,112312928283,14318482495,31178705079,39500671159,35206107319,34920343923]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [26196732291,13362234755,13211243907,13110650243,8698246551,141869463,108311987,74758579]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [57982387,4436829627,4369722811,7651768,26010914239,7651772,30290169283,24427968]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [41204164,41204168,57978319,24424911,57980364,4453537235,4403273171,57980368]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [74756564,74756568,74753503,24422879,91532764,91532768,108308964,21532667371]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [108308968,41197039,41198063,108308972,125085168,8597505527,7574007,125085172]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 125 3 8 = true := by decide +kernel
private theorem i11 : checks ts 125 11 8 = true := by decide +kernel
private theorem i19 : checks ts 125 19 8 = true := by decide +kernel
private theorem i27 : checks ts 125 27 8 = true := by decide +kernel
private theorem i35 : checks ts 125 35 8 = true := by decide +kernel
private theorem i43 : checks ts 125 43 6 = true := by decide +kernel
private theorem rows : checks ts 125 3 46 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 3 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two7wide 2
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [27704236043,35993367575,90838095907,18496008255,30943828159,39349811391,13865558207,17724242279]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [13345459559,4772306279,4537495931,4470389115,175423867,26196662675,13311833491,30440830367]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [376526237,57981351,24427943,7651748,4436829611,141864363,7651752,24427948]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [24427952,57979319,24425911,41204148,41204152,57980348,57980352,74756548]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [74756552,74753487,24422863,91532748,91532752,4436757975,4386428375,108308948]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [25893870043,108305883,74752475,108308952,108308956,125085152,125085156,4352869867]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [125085160,41129455,41196015,141861356,141861360,158637556]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 125 6 8 = true := by decide +kernel
private theorem i14 : checks ts 125 14 8 = true := by decide +kernel
private theorem i22 : checks ts 125 22 8 = true := by decide +kernel
private theorem i30 : checks ts 125 30 8 = true := by decide +kernel
private theorem i38 : checks ts 125 38 8 = true := by decide +kernel
private theorem i46 : checks ts 125 46 3 = true := by decide +kernel
private theorem rows : checks ts 125 6 43 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 4 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two7wide 3
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [27553244175,40019902491,65168959527,26968500283,26649323739,34971223259,8899570011,8798909787]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [259309915,30692491619,22103023971,13362234735,8983385455,4654866799,141866383,91535759]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [57982351,7651736,24427932,24427936,158640551,108309927,74756519,41204132]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [41204136,13194459567,41204140,57980336,57980340,26028418491,74756536,74756540]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [91532736,108306887,57976263,91532740,91532744,4386428367,125083087,108308940]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [108308944,125085140,125085144,125085148,4386425315,4352872931,141861344,74750439]) (by decide +kernel)]
private def p1 : List P := [Compact54FastPrice.fastBatch (unpack [141861348,141861352,158637548,24351219,24352243,158637552,158637556]) (by decide +kernel)]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 125 9 8 = true := by decide +kernel
private theorem i17 : checks ts 125 17 8 = true := by decide +kernel
private theorem i25 : checks ts 125 25 8 = true := by decide +kernel
private theorem i33 : checks ts 125 33 8 = true := by decide +kernel
private theorem i41 : checks ts 125 41 8 = true := by decide +kernel
private theorem rows : checks ts 125 9 40 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 5 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

end Compact50PriceTableTwo7wide
