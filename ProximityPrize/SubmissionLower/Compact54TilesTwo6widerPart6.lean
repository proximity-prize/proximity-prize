import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo6widerPart5

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top7
private abbrev P := PaidBatch .two6wider 7
private def p0 : List P := [⟨Compact54Packed.unpack [60587660317,56261775409,30523085965,26228913293,26179571865,25977662617], by decide +kernel⟩,⟨Compact54Packed.unpack [13076573389,8781806797,30525445373,25995343101,25878368509,12993473789], by decide +kernel⟩,⟨Compact54Packed.unpack [8648047869,4336368909,41338125,12993007897,8698372377,4403539225], by decide +kernel⟩,⟨Compact54Packed.unpack [4319458585,24493337,24625433,7914777,7980316,24360225], by decide +kernel⟩,⟨Compact54Packed.unpack [24557857,24689953,7979297,7980320,24756516], by decide +kernel⟩,⟨Compact54Packed.unpack [41465129,24754473,41532712,7978284], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [24756524,58308912], by decide +kernel⟩,⟨Compact54Packed.unpack [12992279861,8697709877,4402942261,4403337525,4353073461,58108213], by decide +kernel⟩,⟨Compact54Packed.unpack [24554805,24686901,7910708,41531700], by decide +kernel⟩,⟨Compact54Packed.unpack [7980340,7910712,58308920], by decide +kernel⟩,⟨Compact54Packed.unpack [7843133,24686908,41531708], by decide +kernel⟩,⟨Compact54Packed.unpack [7980348,24685888,41530688], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [24756544,41197893,41395525,7842117,7908676], by decide +kernel⟩,⟨Compact54Packed.unpack [7909700,75085124], by decide +kernel⟩,⟨Compact54Packed.unpack [41462088,41530696], by decide +kernel⟩,⟨Compact54Packed.unpack [24756552,41462092,7976268], by decide +kernel⟩,⟨Compact54Packed.unpack [58308940,12992869713,8698299729], by decide +kernel⟩,⟨Compact54Packed.unpack [4403532113,4319582545,24617297,41461072], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [7909712,75085136], by decide +kernel⟩,⟨Compact54Packed.unpack [58238292,24753492], by decide +kernel⟩,⟨Compact54Packed.unpack [41532756,24418649,24616281,7905625], by decide +kernel⟩,⟨Compact54Packed.unpack [58238296,24753496], by decide +kernel⟩,⟨Compact54Packed.unpack [41532760,41460060], by decide +kernel⟩,⟨Compact54Packed.unpack [7908700,75084124], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [7980380,41392481,7904609,41460064], by decide +kernel⟩,⟨Compact54Packed.unpack [7908704,75084128], by decide +kernel⟩,⟨Compact54Packed.unpack [7980384,75013476], by decide +kernel⟩,⟨Compact54Packed.unpack [91861348], by decide +kernel⟩,⟨Compact54Packed.unpack [75013480,7975272], by decide +kernel⟩,⟨Compact54Packed.unpack [75085160,13109319021], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [13110371693,12993394029,4352804205,57838957,24351085,24614253], by decide +kernel⟩,⟨Compact54Packed.unpack [91789676], by decide +kernel⟩,⟨Compact54Packed.unpack [91861356], by decide +kernel⟩,⟨Compact54Packed.unpack [91789680], by decide +kernel⟩,⟨Compact54Packed.unpack [91861360], by decide +kernel⟩,⟨Compact54Packed.unpack [24547701,7902581,58235252], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [7907700,75083124], by decide +kernel⟩,⟨Compact54Packed.unpack [24756596,58234232], by decide +kernel⟩,⟨Compact54Packed.unpack [24683896,58305912], by decide +kernel⟩,⟨Compact54Packed.unpack [41532792,4336289149,41323901,24678781], by decide +kernel⟩,⟨Compact54Packed.unpack [91788668], by decide +kernel⟩,⟨Compact54Packed.unpack [91860348], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [7980412,75011456], by decide +kernel⟩,⟨Compact54Packed.unpack [7907712,75083136], by decide +kernel⟩,⟨Compact54Packed.unpack [24756608,58233220], by decide +kernel⟩,⟨Compact54Packed.unpack [41460100,41528708], by decide +kernel⟩,⟨Compact54Packed.unpack [58308996,4402935177,4403461513], by decide +kernel⟩,⟨Compact54Packed.unpack [4319643017,24677769,58233224], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [41460104,41528712], by decide +kernel⟩,⟨Compact54Packed.unpack [58309000,24678796], by decide +kernel⟩,⟨Compact54Packed.unpack [75012492,7974284], by decide +kernel⟩,⟨Compact54Packed.unpack [91861388], by decide +kernel⟩,⟨Compact54Packed.unpack [24348049,24611217,58232208], by decide +kernel⟩,⟨Compact54Packed.unpack [41459088,41527696], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [75085200,7900564], by decide +kernel⟩,⟨Compact54Packed.unpack [91787668], by decide +kernel⟩,⟨Compact54Packed.unpack [91859348], by decide +kernel⟩,⟨Compact54Packed.unpack [24756628,41387417,7899545,24677784], by decide +kernel⟩,⟨Compact54Packed.unpack [75011480,7973272], by decide +kernel⟩,⟨Compact54Packed.unpack [91860376], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [7980440,75008412], by decide +kernel⟩,⟨Compact54Packed.unpack [41459100,41527708], by decide +kernel⟩,⟨Compact54Packed.unpack [75085212,7899552], by decide +kernel⟩,⟨Compact54Packed.unpack [91786656], by decide +kernel⟩,⟨Compact54Packed.unpack [7906720,75082144], by decide +kernel⟩,⟨Compact54Packed.unpack [41532832,13110171045,12993389989,4403393957], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [24214949,24478117,7898533,41453988], by decide +kernel⟩,⟨Compact54Packed.unpack [58234276,24749476], by decide +kernel⟩,⟨Compact54Packed.unpack [91860388], by decide +kernel⟩,⟨Compact54Packed.unpack [7980452,75007400], by decide +kernel⟩,⟨Compact54Packed.unpack [41458088,41526696], by decide +kernel⟩,⟨Compact54Packed.unpack [91861416], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [24346029,24609197,58230188], by decide +kernel⟩,⟨Compact54Packed.unpack [58234284,24749484], by decide +kernel⟩,⟨Compact54Packed.unpack [91860396], by decide +kernel⟩,⟨Compact54Packed.unpack [7980460,75007408], by decide +kernel⟩,⟨Compact54Packed.unpack [41458096,41526704], by decide +kernel⟩,⟨Compact54Packed.unpack [91861424], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [41319861,7897525,58230196], by decide +kernel⟩,⟨Compact54Packed.unpack [58234292,24749492], by decide +kernel⟩,⟨Compact54Packed.unpack [91860404], by decide +kernel⟩,⟨Compact54Packed.unpack [7980468,75006392], by decide +kernel⟩,⟨Compact54Packed.unpack [58234296,24749496], by decide +kernel⟩,⟨Compact54Packed.unpack [91860408], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [7980472,75006396], by decide +kernel⟩,⟨Compact54Packed.unpack [41457084,41525692], by decide +kernel⟩,⟨Compact54Packed.unpack [91860412], by decide +kernel⟩,⟨Compact54Packed.unpack [7980476,4402734529,4403326401,24147393,24410561,7830977], by decide +kernel⟩,⟨Compact54Packed.unpack [91783616], by decide +kernel⟩,⟨Compact54Packed.unpack [24680896,58302912], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [91861440], by decide +kernel⟩,⟨Compact54Packed.unpack [91782596], by decide +kernel⟩,⟨Compact54Packed.unpack [41457092,41525700], by decide +kernel⟩,⟨Compact54Packed.unpack [91860420], by decide +kernel⟩,⟨Compact54Packed.unpack [7980484,24278473,24541641,41450952], by decide +kernel⟩,⟨Compact54Packed.unpack [91785672], by decide +kernel⟩]
private def p16 : List P := [⟨Compact54Packed.unpack [91857352], by decide +kernel⟩,⟨Compact54Packed.unpack [58309064,24673740], by decide +kernel⟩,⟨Compact54Packed.unpack [91784652], by decide +kernel⟩,⟨Compact54Packed.unpack [7904716,75080140], by decide +kernel⟩,⟨Compact54Packed.unpack [75085260,41252305], by decide +kernel⟩,⟨Compact54Packed.unpack [24672721,75005392], by decide +kernel⟩]
private def p17 : List P := [⟨Compact54Packed.unpack [41456080,41524688], by decide +kernel⟩,⟨Compact54Packed.unpack [91859408], by decide +kernel⟩,⟨Compact54Packed.unpack [24756688,58228180], by decide +kernel⟩,⟨Compact54Packed.unpack [58232276,24747476], by decide +kernel⟩,⟨Compact54Packed.unpack [91858388], by decide +kernel⟩,⟨Compact54Packed.unpack [41532884,41449944], by decide +kernel⟩]
private def p18 : List P := [⟨Compact54Packed.unpack [91784664], by decide +kernel⟩,⟨Compact54Packed.unpack [91856344], by decide +kernel⟩,⟨Compact54Packed.unpack [75085272], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15 ++ p16 ++ p17 ++ p18
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 118 21 8 = true := by decide +kernel
private theorem i29 : checks ts 118 29 8 = true := by decide +kernel
private theorem i37 : checks ts 118 37 8 = true := by decide +kernel
private theorem i45 : checks ts 118 45 5 = true := by decide +kernel
private theorem rows : checks ts 118 21 29 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 9 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

end Compact50PriceTableTwo6wider
