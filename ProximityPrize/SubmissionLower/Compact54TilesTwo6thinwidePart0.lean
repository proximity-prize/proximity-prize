import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6thin

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top1
private abbrev P := PaidBatch .two6thinwide 1
private def p0 : List P := [⟨Compact54Packed.unpack [47497415685,47699082261,94945897509,47498660933,21727612037,21727683717], by decide +kernel⟩,⟨Compact54Packed.unpack [47767960709,47701126293,43406302357,21727939781,21728076997,21728333061], by decide +kernel⟩,⟨Compact54Packed.unpack [21728535813,47500442885,47500848389,43206221061,21728726341,21728929093], by decide +kernel⟩,⟨Compact54Packed.unpack [21729459525,21730055493,21730585925,21731116357,21731581253,17436882245], by decide +kernel⟩,⟨Compact54Packed.unpack [21729054085,21729322373,21729983877,21730710917,21731372421,21597357445], by decide +kernel⟩,⟨Compact54Packed.unpack [8712330629,8712595845,8645490053,4350525829,4350522773,55557525], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [4317102485,22069661,22201757,8712127909,8712393125,8712723877], by decide +kernel⟩,⟨Compact54Packed.unpack [4350519717,55488933,4317099429,22134181,22200741,5424548], by decide +kernel⟩,⟨Compact54Packed.unpack [5424552,22066605,22133165,5422509,22200748], by decide +kernel⟩,⟨Compact54Packed.unpack [38976944,4317096373,55751093,22197685], by decide +kernel⟩,⟨Compact54Packed.unpack [5421493,38976948,22198712], by decide +kernel⟩,⟨Compact54Packed.unpack [22200760,21998013,22064573,5420477,5421500], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [38976956,38974912], by decide +kernel⟩,⟨Compact54Packed.unpack [22200768,21729447365,21729781189,21730573765,21731366341], by decide +kernel⟩,⟨Compact54Packed.unpack [21597547973,8712455621,8645546437,4350647749,55616965,22063557], by decide +kernel⟩,⟨Compact54Packed.unpack [22195653,72528324], by decide +kernel⟩,⟨Compact54Packed.unpack [5424580,72528328], by decide +kernel⟩,⟨Compact54Packed.unpack [5424584,5351885,55750092], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [38976972,5351888,22195664], by decide +kernel⟩,⟨Compact54Packed.unpack [72529360,4350513621], by decide +kernel⟩,⟨Compact54Packed.unpack [55482837,21929429,22061525,5350869,5351892,5418452], by decide +kernel⟩,⟨Compact54Packed.unpack [89305556], by decide +kernel⟩,⟨Compact54Packed.unpack [22128088,55750104], by decide +kernel⟩,⟨Compact54Packed.unpack [38976984,22060509,5349853,5350876], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [5351900,72527324], by decide +kernel⟩,⟨Compact54Packed.unpack [22200796,38904288,5418464], by decide +kernel⟩,⟨Compact54Packed.unpack [89305568], by decide +kernel⟩,⟨Compact54Packed.unpack [8712056293,8712452581,8645543397,4317024741,55679461,5348837], by decide +kernel⟩,⟨Compact54Packed.unpack [22127076,55749092], by decide +kernel⟩,⟨Compact54Packed.unpack [55753188,22126056], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5350888,72526312], by decide +kernel⟩,⟨Compact54Packed.unpack [38977000,21860845,21992941,5348844], by decide +kernel⟩,⟨Compact54Packed.unpack [22127084,55749100], by decide +kernel⟩,⟨Compact54Packed.unpack [55753196,22126064], by decide +kernel⟩,⟨Compact54Packed.unpack [5350896,72526320], by decide +kernel⟩,⟨Compact54Packed.unpack [38977008,4350445045,55479797,21991925], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [22124021,55679476,5417460], by decide +kernel⟩,⟨Compact54Packed.unpack [89304564], by decide +kernel⟩,⟨Compact54Packed.unpack [5424628,55679480,5417464], by decide +kernel⟩,⟨Compact54Packed.unpack [89304568], by decide +kernel⟩,⟨Compact54Packed.unpack [5424632,22057469,5346813,38902268], by decide +kernel⟩,⟨Compact54Packed.unpack [5350908,72526332], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [38977020,38901248], by decide +kernel⟩,⟨Compact54Packed.unpack [22127104,55749120], by decide +kernel⟩,⟨Compact54Packed.unpack [55753216], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 128 3 8 = true := by decide +kernel
private theorem i11 : checks ts 128 11 8 = true := by decide +kernel
private theorem i19 : checks ts 128 19 8 = true := by decide +kernel
private theorem i27 : checks ts 128 27 8 = true := by decide +kernel
private theorem i35 : checks ts 128 35 8 = true := by decide +kernel
private theorem i43 : checks ts 128 43 7 = true := by decide +kernel
private theorem rows : checks ts 128 3 47 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 3 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6thinwide 2
private def p0 : List P := [⟨Compact54Packed.unpack [43471476745,43404248089,90651258921,43473049737,43472995465,43406291097], by decide +kernel⟩,⟨Compact54Packed.unpack [43406695577,43205466377,43474699529,43206013193,43206614281,21728729417], by decide +kernel⟩,⟨Compact54Packed.unpack [17433964873,21730849097,17436215625,21731843401,17302402377,8712598889], by decide +kernel⟩,⟨Compact54Packed.unpack [4417700201,21729122697,17434358153,21730313609,17435745673,21731635593], by decide +kernel⟩,⟨Compact54Packed.unpack [17302456713,8712527241,8645486985,4350588297,55557513,4317168009], by decide +kernel⟩,⟨Compact54Packed.unpack [22069649,22201745,4350519705,55488921,4317099417,22134169], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [22200729,5424536,5424540,22066593,22133153,5422497], by decide +kernel⟩,⟨Compact54Packed.unpack [22200736,38976932,8712391081], by decide +kernel⟩,⟨Compact54Packed.unpack [4417492393,8645615017,4317030825,55751081,22197673,5421481], by decide +kernel⟩,⟨Compact54Packed.unpack [38976936,38975916], by decide +kernel⟩,⟨Compact54Packed.unpack [5424556,21998001,22064561,5420465,22198704], by decide +kernel⟩,⟨Compact54Packed.unpack [22200752,55752116], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [5424564,4350582201,55616953,22063545,5352889,5419448], by decide +kernel⟩,⟨Compact54Packed.unpack [72529336,5352892], by decide +kernel⟩,⟨Compact54Packed.unpack [89305532], by decide +kernel⟩,⟨Compact54Packed.unpack [5351873,72527296], by decide +kernel⟩,⟨Compact54Packed.unpack [22200768,5351876,38972868], by decide +kernel⟩,⟨Compact54Packed.unpack [55753156,21712673225,17417974217], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [21714060745,17419558345,8711991753,8712388041,8645478857,4350580169], by decide +kernel⟩,⟨Compact54Packed.unpack [21929417,22061513,5350857,5351880,22195656], by decide +kernel⟩,⟨Compact54Packed.unpack [72529352,5350860], by decide +kernel⟩,⟨Compact54Packed.unpack [5351884,72527308], by decide +kernel⟩,⟨Compact54Packed.unpack [22200780,22060497,22127057,22128080], by decide +kernel⟩,⟨Compact54Packed.unpack [89304528], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [5424592,22128084,38972884], by decide +kernel⟩,⟨Compact54Packed.unpack [55753172,4350380505,55415257], by decide +kernel⟩,⟨Compact54Packed.unpack [4317091289,22126041,38904280,5418456], by decide +kernel⟩,⟨Compact54Packed.unpack [89305560], by decide +kernel⟩,⟨Compact54Packed.unpack [38904284,38972892], by decide +kernel⟩,⟨Compact54Packed.unpack [55753180,21992929,22125025], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [55680480,22195680], by decide +kernel⟩,⟨Compact54Packed.unpack [72529376,5348836], by decide +kernel⟩,⟨Compact54Packed.unpack [22127076,55749092], by decide +kernel⟩,⟨Compact54Packed.unpack [55753188,8695476713,8695873001], by decide +kernel⟩,⟨Compact54Packed.unpack [4350577129,55611881,22058473,5347817,22126056], by decide +kernel⟩,⟨Compact54Packed.unpack [5350888,72526312], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [38977000,38902252], by decide +kernel⟩,⟨Compact54Packed.unpack [5350892,72526316], by decide +kernel⟩,⟨Compact54Packed.unpack [38977004,5346801,22125040], by decide +kernel⟩,⟨Compact54Packed.unpack [22127088,55749104], by decide +kernel⟩,⟨Compact54Packed.unpack [55753200,22124020], by decide +kernel⟩,⟨Compact54Packed.unpack [38903284,38971892], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [72529396,38636025], by decide +kernel⟩,⟨Compact54Packed.unpack [38833657,22123001,55678456], by decide +kernel⟩,⟨Compact54Packed.unpack [5350904,72526328], by decide +kernel⟩,⟨Compact54Packed.unpack [38977016,38901244], by decide +kernel⟩,⟨Compact54Packed.unpack [22127100,55749116], by decide +kernel⟩,⟨Compact54Packed.unpack [55753212,22123008], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [55679488,22194688], by decide +kernel⟩,⟨Compact54Packed.unpack [89305600], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 128 6 8 = true := by decide +kernel
private theorem i14 : checks ts 128 14 8 = true := by decide +kernel
private theorem i22 : checks ts 128 22 8 = true := by decide +kernel
private theorem i30 : checks ts 128 30 8 = true := by decide +kernel
private theorem i38 : checks ts 128 38 8 = true := by decide +kernel
private theorem i46 : checks ts 128 46 4 = true := by decide +kernel
private theorem rows : checks ts 128 6 44 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 4 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6thinwide 3
private def p0 : List P := [⟨Compact54Packed.unpack [86423249933,82061391913,43456144525,39161254029,39111456921,39111860377], by decide +kernel⟩,⟨Compact54Packed.unpack [43474429193,39179669769,38911113481,38911713545,17435949385,17436413257], by decide +kernel⟩,⟨Compact54Packed.unpack [17436877129,17302598985,8712729961,4417831273,21729322377,17434754441], by decide +kernel⟩,⟨Compact54Packed.unpack [17435414921,17436075401,17436670345,8712195465,4417296777,8712724873], by decide +kernel⟩,⟨Compact54Packed.unpack [4350520713,4350719369,55688585,22135177,22201737,5423505], by decide +kernel⟩,⟨Compact54Packed.unpack [5424528,22200724,4317097369,22066585,22198681], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [5422489,22200728,38976924], by decide +kernel⟩,⟨Compact54Packed.unpack [21999009,22065569,22197665,38975904], by decide +kernel⟩,⟨Compact54Packed.unpack [5424544,55753124,8712588713], by decide +kernel⟩,⟨Compact54Packed.unpack [4417690025,4350648745,55617961,22064553,22196649,5420456], by decide +kernel⟩,⟨Compact54Packed.unpack [55753128,22197676], by decide +kernel⟩,⟨Compact54Packed.unpack [38976940,5352881,22196656], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [55753136,5352884,5419444], by decide +kernel⟩,⟨Compact54Packed.unpack [72529332,21930425], by decide +kernel⟩,⟨Compact54Packed.unpack [22062521,5351865,5352888,38973880], by decide +kernel⟩,⟨Compact54Packed.unpack [38976952,22129084,5419452], by decide +kernel⟩,⟨Compact54Packed.unpack [72529340,22061505], by decide +kernel⟩,⟨Compact54Packed.unpack [5350849,5351872,55750080], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [38976960,22128068,5418436], by decide +kernel⟩,⟨Compact54Packed.unpack [89305540], by decide +kernel⟩,⟨Compact54Packed.unpack [21712938441,17418436041,17419162057,17419888073,8712255945,4417422793], by decide +kernel⟩,⟨Compact54Packed.unpack [4350381513,55416265,21928393,21994953,22127049,5350856], by decide +kernel⟩,⟨Compact54Packed.unpack [5351880,72527304], by decide +kernel⟩,⟨Compact54Packed.unpack [22200776,22128076,22195660], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [72529356,21993937], by decide +kernel⟩,⟨Compact54Packed.unpack [22126033,38904272,22195664], by decide +kernel⟩,⟨Compact54Packed.unpack [72529360,5349844], by decide +kernel⟩,⟨Compact54Packed.unpack [22128084,55750100], by decide +kernel⟩,⟨Compact54Packed.unpack [38976980,4350578137,55612889,22059481], by decide +kernel⟩,⟨Compact54Packed.unpack [55680472,22195672], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [72529368,5348828], by decide +kernel⟩,⟨Compact54Packed.unpack [38904284,38972892], by decide +kernel⟩,⟨Compact54Packed.unpack [55753180,5347809,5348832], by decide +kernel⟩,⟨Compact54Packed.unpack [38904288,38972896], by decide +kernel⟩,⟨Compact54Packed.unpack [55753184,22125028], by decide +kernel⟩,⟨Compact54Packed.unpack [22127076,55749092], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [55753188,8695806441,4400973289], by decide +kernel⟩,⟨Compact54Packed.unpack [21859817,21991913,22124009,38902248], by decide +kernel⟩,⟨Compact54Packed.unpack [5350888,72526312], by decide +kernel⟩,⟨Compact54Packed.unpack [38977000,38902252], by decide +kernel⟩,⟨Compact54Packed.unpack [5350892,72526316], by decide +kernel⟩,⟨Compact54Packed.unpack [38977004,21925361,22122993,5346800], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [55679472,22194672], by decide +kernel⟩,⟨Compact54Packed.unpack [89305584], by decide +kernel⟩,⟨Compact54Packed.unpack [72455668,5417460], by decide +kernel⟩,⟨Compact54Packed.unpack [89304564], by decide +kernel⟩,⟨Compact54Packed.unpack [5424628,38833657,5345785,38901240], by decide +kernel⟩,⟨Compact54Packed.unpack [22127096,55749112], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [55753208,22123004], by decide +kernel⟩,⟨Compact54Packed.unpack [55679484,22194684], by decide +kernel⟩,⟨Compact54Packed.unpack [89305596], by decide +kernel⟩,⟨Compact54Packed.unpack [89231872], by decide +kernel⟩,⟨Compact54Packed.unpack [89303552], by decide +kernel⟩,⟨Compact54Packed.unpack [22200832], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 128 9 8 = true := by decide +kernel
private theorem i17 : checks ts 128 17 8 = true := by decide +kernel
private theorem i25 : checks ts 128 25 8 = true := by decide +kernel
private theorem i33 : checks ts 128 33 8 = true := by decide +kernel
private theorem i41 : checks ts 128 41 8 = true := by decide +kernel
private theorem i49 : checks ts 128 49 1 = true := by decide +kernel
private theorem rows : checks ts 128 9 41 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 5 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

end Compact50PriceTableTwo6thinwide
