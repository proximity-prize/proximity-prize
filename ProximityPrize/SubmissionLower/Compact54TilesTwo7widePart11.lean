/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact54Packed

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

namespace Top12
private abbrev P := PaidBatch .two7wide 12
private def p0 : List P := [⟨Compact54Packed.unpack [52016615473,25993842853,21699603621,25995219165,21582884061,8697720057], by decide +kernel⟩,⟨Compact54Packed.unpack [8698181881,13009260821,8714690837,8647716117,4352948501,57983253], by decide +kernel⟩,⟨Compact54Packed.unpack [4352814373,57849125,24295717,24427813,7651620,7651624], by decide +kernel⟩,⟨Compact54Packed.unpack [7584045,24427820,41204016], by decide +kernel⟩,⟨Compact54Packed.unpack [12993073461,4352549173,57583925,4319391029,24425781,7649588], by decide +kernel⟩,⟨Compact54Packed.unpack [24427828,41204024,24227133], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [24424765,57980220,7648576], by decide +kernel⟩,⟨Compact54Packed.unpack [41204032,4336034117,41068869,24423749], by decide +kernel⟩,⟨Compact54Packed.unpack [74756420,7647560], by decide +kernel⟩,⟨Compact54Packed.unpack [57980232,24423756], by decide +kernel⟩,⟨Compact54Packed.unpack [57980236,4402876753,4352743761], by decide +kernel⟩,⟨Compact54Packed.unpack [24027473,24290641,7579985,41200976], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [41204048,41199956], by decide +kernel⟩,⟨Compact54Packed.unpack [57980244,24224089,24421721], by decide +kernel⟩,⟨Compact54Packed.unpack [91531608], by decide +kernel⟩,⟨Compact54Packed.unpack [7651672,74754396], by decide +kernel⟩,⟨Compact54Packed.unpack [24427868,40802657,41000289,24355169,7644512], by decide +kernel⟩,⟨Compact54Packed.unpack [91531616], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [7651680,74753380], by decide +kernel⟩,⟨Compact54Packed.unpack [41204068,7577960,24421736], by decide +kernel⟩,⟨Compact54Packed.unpack [91532648], by decide +kernel⟩,⟨Compact54Packed.unpack [4352807277,24156525,7511405,7577964,24421740], by decide +kernel⟩,⟨Compact54Packed.unpack [91532652], by decide +kernel⟩,⟨Compact54Packed.unpack [24354160,57976176], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [57980272,24353141,7576948], by decide +kernel⟩,⟨Compact54Packed.unpack [91529588], by decide +kernel⟩,⟨Compact54Packed.unpack [41204084,7576952,24420728], by decide +kernel⟩,⟨Compact54Packed.unpack [91531640], by decide +kernel⟩,⟨Compact54Packed.unpack [7651704,40866173,41129341,24353148,7643516], by decide +kernel⟩,⟨Compact54Packed.unpack [91530620], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [24427900,24353152,24420736], by decide +kernel⟩,⟨Compact54Packed.unpack [91531648], by decide +kernel⟩,⟨Compact54Packed.unpack [7651712,24353156,41197956], by decide +kernel⟩,⟨Compact54Packed.unpack [91532676], by decide +kernel⟩,⟨Compact54Packed.unpack [24220041,41129352,24420744], by decide +kernel⟩,⟨Compact54Packed.unpack [91531656], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [7651720,41129356,24420748], by decide +kernel⟩,⟨Compact54Packed.unpack [91531660], by decide +kernel⟩,⟨Compact54Packed.unpack [7651724,7573905,41129360,7643536], by decide +kernel⟩,⟨Compact54Packed.unpack [91530640], by decide +kernel⟩,⟨Compact54Packed.unpack [24427920,57905556], by decide +kernel⟩,⟨Compact54Packed.unpack [91529620], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [41204116,41128344], by decide +kernel⟩,⟨Compact54Packed.unpack [7576984,74752408], by decide +kernel⟩,⟨Compact54Packed.unpack [57980312,24351132], by decide +kernel⟩,⟨Compact54Packed.unpack [24353180,57975196], by decide +kernel⟩,⟨Compact54Packed.unpack [74756508,7573920], by decide +kernel⟩,⟨Compact54Packed.unpack [41129376,41197984], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [91532704], by decide +kernel⟩,⟨Compact54Packed.unpack [57905572,24420772], by decide +kernel⟩,⟨Compact54Packed.unpack [91531684], by decide +kernel⟩,⟨Compact54Packed.unpack [7651748,41128360,24419752], by decide +kernel⟩,⟨Compact54Packed.unpack [91530664], by decide +kernel⟩,⟨Compact54Packed.unpack [24427944,41128364,7642540], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [91529644], by decide +kernel⟩,⟨Compact54Packed.unpack [41204140,41128368], by decide +kernel⟩,⟨Compact54Packed.unpack [91528624], by decide +kernel⟩,⟨Compact54Packed.unpack [57980336,24351156], by decide +kernel⟩,⟨Compact54Packed.unpack [7575988,74751412], by decide +kernel⟩,⟨Compact54Packed.unpack [74756532,7573944], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [24352184,57974200], by decide +kernel⟩,⟨Compact54Packed.unpack [91532728], by decide +kernel⟩,⟨Compact54Packed.unpack [41128380,41196988], by decide +kernel⟩,⟨Compact54Packed.unpack [91531708], by decide +kernel⟩,⟨Compact54Packed.unpack [7651772,41128384,24419776], by decide +kernel⟩,⟨Compact54Packed.unpack [91530688], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [24427968,41128388,7642564], by decide +kernel⟩,⟨Compact54Packed.unpack [91529668], by decide +kernel⟩,⟨Compact54Packed.unpack [41204164,41128392], by decide +kernel⟩,⟨Compact54Packed.unpack [91528648], by decide +kernel⟩,⟨Compact54Packed.unpack [57980360,24351180], by decide +kernel⟩,⟨Compact54Packed.unpack [7576012,74751436], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [74756556,7573968], by decide +kernel⟩,⟨Compact54Packed.unpack [24352208,57974224], by decide +kernel⟩,⟨Compact54Packed.unpack [91532752], by decide +kernel⟩,⟨Compact54Packed.unpack [41128404,41197012], by decide +kernel⟩,⟨Compact54Packed.unpack [91531732], by decide +kernel⟩,⟨Compact54Packed.unpack [7651796,24351192,41195992], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [91530712], by decide +kernel⟩,⟨Compact54Packed.unpack [24427992,24351196,24418780], by decide +kernel⟩,⟨Compact54Packed.unpack [91529692], by decide +kernel⟩,⟨Compact54Packed.unpack [41204188,24351200,7641568], by decide +kernel⟩,⟨Compact54Packed.unpack [91528672], by decide +kernel⟩,⟨Compact54Packed.unpack [57980384,24351204], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [91527652], by decide +kernel⟩,⟨Compact54Packed.unpack [74756580,7573992], by decide +kernel⟩,⟨Compact54Packed.unpack [7575016,74750440], by decide +kernel⟩,⟨Compact54Packed.unpack [91532776], by decide +kernel⟩,⟨Compact54Packed.unpack [24351212,57973228], by decide +kernel⟩,⟨Compact54Packed.unpack [91531756], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [7651820,24351216,41196016], by decide +kernel⟩,⟨Compact54Packed.unpack [91530736], by decide +kernel⟩,⟨Compact54Packed.unpack [24428016,24351220,24418804], by decide +kernel⟩,⟨Compact54Packed.unpack [91529716], by decide +kernel⟩,⟨Compact54Packed.unpack [41204212], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 125 36 8 = true := by decide +kernel
private theorem i44 : checks ts 125 44 5 = true := by decide +kernel
private theorem rows : checks ts 125 36 13 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 14 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo7wide
