import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo6widerPart8

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top10
private abbrev P := PaidBatch .two6wider 10
private def p0 : List P := [⟨Compact54Packed.unpack [39112505385,39047635001,39098349721,38880125081,17388314833,17389106385], by decide +kernel⟩,⟨Compact54Packed.unpack [17404623109,17405611269,17288372485,8647914757,4353147141,4336170261], by decide +kernel⟩,⟨Compact54Packed.unpack [41205013,41337109,41534741,8698372385,4352945441,4319589665], by decide +kernel⟩,⟨Compact54Packed.unpack [24624417,7913761,7980320,24756516,24425769], by decide +kernel⟩,⟨Compact54Packed.unpack [24623401,7912745,24756520,24755500], by decide +kernel⟩,⟨Compact54Packed.unpack [7980332,41135409,41333041,24622385,7977265,7978288], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [24756528,58308916], by decide +kernel⟩,⟨Compact54Packed.unpack [7910712,58308920,17388894525], by decide +kernel⟩,⟨Compact54Packed.unpack [8697974077,4403206461,4353007933,58042685,24554813,7844157], by decide +kernel⟩,⟨Compact54Packed.unpack [7910716,58308924,7909696], by decide +kernel⟩,⟨Compact54Packed.unpack [75085120,24685893], by decide +kernel⟩,⟨Compact54Packed.unpack [7909700,75085124], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [7909704,75085128], by decide +kernel⟩,⟨Compact54Packed.unpack [41132365,41329997,24684877,24685900,7976268], by decide +kernel⟩,⟨Compact54Packed.unpack [58308940,24685904], by decide +kernel⟩,⟨Compact54Packed.unpack [75085136,7907668], by decide +kernel⟩,⟨Compact54Packed.unpack [24685908,58307924], by decide +kernel⟩,⟨Compact54Packed.unpack [7980372,8681655641,4336359769,41394521,7906649,7907672], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [24685912,58307928], by decide +kernel⟩,⟨Compact54Packed.unpack [7980376,41461084,24752476], by decide +kernel⟩,⟨Compact54Packed.unpack [58308956,24683872], by decide +kernel⟩,⟨Compact54Packed.unpack [7908704,75084128], by decide +kernel⟩,⟨Compact54Packed.unpack [7980384,41195877,41393509,7905637,24683876], by decide +kernel⟩,⟨Compact54Packed.unpack [7908708,75084132], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [7980388,58237288,7975272], by decide +kernel⟩,⟨Compact54Packed.unpack [75085160,7905644], by decide +kernel⟩,⟨Compact54Packed.unpack [41461100,41529708], by decide +kernel⟩,⟨Compact54Packed.unpack [41532780,8697837937,4403135857,4353002865], by decide +kernel⟩,⟨Compact54Packed.unpack [58037617,24615281,58236272], by decide +kernel⟩,⟨Compact54Packed.unpack [7908720,75084144], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [7980400,58236276,7974260], by decide +kernel⟩,⟨Compact54Packed.unpack [91861364], by decide +kernel⟩,⟨Compact54Packed.unpack [7903609,58236280,7974264], by decide +kernel⟩,⟨Compact54Packed.unpack [91861368], by decide +kernel⟩,⟨Compact54Packed.unpack [75012476,7974268], by decide +kernel⟩,⟨Compact54Packed.unpack [91861372], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [41061761,41259393,24679809,41458048], by decide +kernel⟩,⟨Compact54Packed.unpack [24683904,58305920], by decide +kernel⟩,⟨Compact54Packed.unpack [41532800,41458052], by decide +kernel⟩,⟨Compact54Packed.unpack [24683908,58305924], by decide +kernel⟩,⟨Compact54Packed.unpack [41532804,41457032], by decide +kernel⟩,⟨Compact54Packed.unpack [41460104,41528712], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [58309000,8698362253,4353066381], by decide +kernel⟩,⟨Compact54Packed.unpack [24415629,24678797,58234252], by decide +kernel⟩,⟨Compact54Packed.unpack [24683916,58305932], by decide +kernel⟩,⟨Compact54Packed.unpack [41532812,41457040], by decide +kernel⟩,⟨Compact54Packed.unpack [24682896,58304912], by decide +kernel⟩,⟨Compact54Packed.unpack [58309008,24546709,7901588], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [75011476,7973268], by decide +kernel⟩,⟨Compact54Packed.unpack [91860372], by decide +kernel⟩,⟨Compact54Packed.unpack [7980436,75010456], by decide +kernel⟩,⟨Compact54Packed.unpack [7906712,75082136], by decide +kernel⟩,⟨Compact54Packed.unpack [41532824,41059741,41322909,7835037], by decide +kernel⟩,⟨Compact54Packed.unpack [91787676], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [91859356], by decide +kernel⟩,⟨Compact54Packed.unpack [24756636,58232224], by decide +kernel⟩,⟨Compact54Packed.unpack [41459104,41527712], by decide +kernel⟩,⟨Compact54Packed.unpack [75085216,7900580], by decide +kernel⟩,⟨Compact54Packed.unpack [75010468,7972260], by decide +kernel⟩,⟨Compact54Packed.unpack [91859364], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [24756644,4352801193,57835945,24413609,24676777], by decide +kernel⟩,⟨Compact54Packed.unpack [91786664], by decide +kernel⟩,⟨Compact54Packed.unpack [91858344], by decide +kernel⟩,⟨Compact54Packed.unpack [41532840,41455020], by decide +kernel⟩,⟨Compact54Packed.unpack [41458092,41526700], by decide +kernel⟩,⟨Compact54Packed.unpack [91861420], by decide +kernel⟩]
private def p11 : List P := [⟨Compact54Packed.unpack [24544689,75008432], by decide +kernel⟩,⟨Compact54Packed.unpack [24681904,58303920], by decide +kernel⟩,⟨Compact54Packed.unpack [75085232,7899572], by decide +kernel⟩,⟨Compact54Packed.unpack [91786676], by decide +kernel⟩,⟨Compact54Packed.unpack [91858356], by decide +kernel⟩,⟨Compact54Packed.unpack [41532852,4336220601,41255353,24675769], by decide +kernel⟩]
private def p12 : List P := [⟨Compact54Packed.unpack [91785656], by decide +kernel⟩,⟨Compact54Packed.unpack [7905720,75081144], by decide +kernel⟩,⟨Compact54Packed.unpack [58309048,24676796], by decide +kernel⟩,⟨Compact54Packed.unpack [58233276,24748476], by decide +kernel⟩,⟨Compact54Packed.unpack [91859388], by decide +kernel⟩,⟨Compact54Packed.unpack [24756668,58230208], by decide +kernel⟩]
private def p13 : List P := [⟨Compact54Packed.unpack [41457088,41525696], by decide +kernel⟩,⟨Compact54Packed.unpack [91860416], by decide +kernel⟩,⟨Compact54Packed.unpack [7980480,4336417221,41451973,41452996], by decide +kernel⟩,⟨Compact54Packed.unpack [58233284,24748484], by decide +kernel⟩,⟨Compact54Packed.unpack [91859396], by decide +kernel⟩,⟨Compact54Packed.unpack [24756676,58230216], by decide +kernel⟩]
private def p14 : List P := [⟨Compact54Packed.unpack [41457096,41525704], by decide +kernel⟩,⟨Compact54Packed.unpack [91860424], by decide +kernel⟩,⟨Compact54Packed.unpack [7980488,75007436], by decide +kernel⟩,⟨Compact54Packed.unpack [24680908,58302924], by decide +kernel⟩,⟨Compact54Packed.unpack [91861452], by decide +kernel⟩,⟨Compact54Packed.unpack [41122257,41385425,58229200], by decide +kernel⟩]
private def p15 : List P := [⟨Compact54Packed.unpack [41456080,41524688], by decide +kernel⟩,⟨Compact54Packed.unpack [91859408], by decide +kernel⟩,⟨Compact54Packed.unpack [24756688,58229204], by decide +kernel⟩,⟨Compact54Packed.unpack [41456084,41524692], by decide +kernel⟩,⟨Compact54Packed.unpack [91859412], by decide +kernel⟩,⟨Compact54Packed.unpack [24756692,58229208], by decide +kernel⟩]
private def p16 : List P := [⟨Compact54Packed.unpack [41456088,41524696], by decide +kernel⟩,⟨Compact54Packed.unpack [91859416], by decide +kernel⟩,⟨Compact54Packed.unpack [24756696], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10 ++ p11 ++ p12 ++ p13 ++ p14 ++ p15 ++ p16
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 118 30 8 = true := by decide +kernel
private theorem i38 : checks ts 118 38 8 = true := by decide +kernel
private theorem i46 : checks ts 118 46 4 = true := by decide +kernel
private theorem rows : checks ts 118 30 20 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 12 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

end Compact50PriceTableTwo6wider
