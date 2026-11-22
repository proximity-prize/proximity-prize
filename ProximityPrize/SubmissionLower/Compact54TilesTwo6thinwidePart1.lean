/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact54Packed

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

namespace Top4
private abbrev P := PaidBatch .two6thinwide 4
private def p0 : List P := [⟨Compact54Packed.unpack [77832728593,77766556717,39160918161,34866288785,39111654557,34817090717], by decide +kernel⟩,⟨Compact54Packed.unpack [39162294541,34867796237,38911376653,17436222733,13141457165,17419304269], by decide +kernel⟩,⟨Compact54Packed.unpack [17419833677,17302463821,13007698253,8695686509,4400853357,4400986477], by decide +kernel⟩,⟨Compact54Packed.unpack [4350656877,38912381,38978941,38911291785,17435679113,13141044617], by decide +kernel⟩,⟨Compact54Packed.unpack [17302257033,8712393097,4417494409,8645617033,4317032841,22067593], by decide +kernel⟩,⟨Compact54Packed.unpack [22134153,5423497,5424520,22200716,21934481], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [22066577,22198673,5422481,22200720,5422484], by decide +kernel⟩,⟨Compact54Packed.unpack [22200724,4350584217,55618969,22065561,22197657], by decide +kernel⟩,⟨Compact54Packed.unpack [5421465,38976920,22198684], by decide +kernel⟩,⟨Compact54Packed.unpack [22200732,22196641,38974880], by decide +kernel⟩,⟨Compact54Packed.unpack [22200736,55752100], by decide +kernel⟩,⟨Compact54Packed.unpack [5424548,8712125865,4417227177,8712720809,4350582185,21931433], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [22063529,5352873,55751080], by decide +kernel⟩,⟨Compact54Packed.unpack [22200744,5352876,38973868], by decide +kernel⟩,⟨Compact54Packed.unpack [38976940,22062513,22129073,5352880], by decide +kernel⟩,⟨Compact54Packed.unpack [89305520], by decide +kernel⟩,⟨Compact54Packed.unpack [5352884,72528308], by decide +kernel⟩,⟨Compact54Packed.unpack [5424564,4317093305,22128057,22129080,5419448], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [72529336,5351868], by decide +kernel⟩,⟨Compact54Packed.unpack [5352892,72528316], by decide +kernel⟩,⟨Compact54Packed.unpack [5424572,21994945,22127041,22128064,5418432], by decide +kernel⟩,⟨Compact54Packed.unpack [89305536], by decide +kernel⟩,⟨Compact54Packed.unpack [22128068,55750084], by decide +kernel⟩,⟨Compact54Packed.unpack [38976964,17417908681,17418700233,17419426249], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [13124857289,8712453577,4417620425,4350579145,55613897,22060489], by decide +kernel⟩,⟨Compact54Packed.unpack [38904264,38972872], by decide +kernel⟩,⟨Compact54Packed.unpack [55753160,22127052], by decide +kernel⟩,⟨Compact54Packed.unpack [5351884,72527308], by decide +kernel⟩,⟨Compact54Packed.unpack [22200780,5348817,38904272], by decide +kernel⟩,⟨Compact54Packed.unpack [89304528], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5424592,55680468,5418452], by decide +kernel⟩,⟨Compact54Packed.unpack [89305556], by decide +kernel⟩,⟨Compact54Packed.unpack [4317090265,22125017,55680472], by decide +kernel⟩,⟨Compact54Packed.unpack [89304536], by decide +kernel⟩,⟨Compact54Packed.unpack [5424600,55680476,5418460], by decide +kernel⟩,⟨Compact54Packed.unpack [89305564], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [21926369,22124001,55679456], by decide +kernel⟩,⟨Compact54Packed.unpack [5351904,72527328], by decide +kernel⟩,⟨Compact54Packed.unpack [22200800,55679460], by decide +kernel⟩,⟨Compact54Packed.unpack [89303524], by decide +kernel⟩,⟨Compact54Packed.unpack [22200804,8645541353,4350642665,22057449,5346793], by decide +kernel⟩,⟨Compact54Packed.unpack [55679464,22194664], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [89305576], by decide +kernel⟩,⟨Compact54Packed.unpack [72455660,5417452], by decide +kernel⟩,⟨Compact54Packed.unpack [89304556], by decide +kernel⟩,⟨Compact54Packed.unpack [5424620,22122993,55678448], by decide +kernel⟩,⟨Compact54Packed.unpack [5350896,72526320], by decide +kernel⟩,⟨Compact54Packed.unpack [38977008,38901236], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [22127092,55749108], by decide +kernel⟩,⟨Compact54Packed.unpack [55753204,4333600249,38569465], by decide +kernel⟩,⟨Compact54Packed.unpack [38767097,38899193,55677432], by decide +kernel⟩,⟨Compact54Packed.unpack [22127096,55749112], by decide +kernel⟩,⟨Compact54Packed.unpack [55753208,22123004], by decide +kernel⟩,⟨Compact54Packed.unpack [55679484,22194684], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [89305596], by decide +kernel⟩,⟨Compact54Packed.unpack [89231872], by decide +kernel⟩,⟨Compact54Packed.unpack [89303552], by decide +kernel⟩,⟨Compact54Packed.unpack [22200832], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 128 12 8 = true := by decide +kernel
private theorem i20 : checks ts 128 20 8 = true := by decide +kernel
private theorem i28 : checks ts 128 28 8 = true := by decide +kernel
private theorem i36 : checks ts 128 36 8 = true := by decide +kernel
private theorem i44 : checks ts 128 44 6 = true := by decide +kernel
private theorem rows : checks ts 128 12 38 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 6 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6thinwide 5
private def p0 : List P := [⟨Compact54Packed.unpack [73520790549,69176624173,34865888401,34866487441,34816754845,30522124445], by decide +kernel⟩,⟨Compact54Packed.unpack [34867133709,34868060429,34616345869,30187104525,13007038765,13007305005], by decide +kernel⟩,⟨Compact54Packed.unpack [17419568461,13124868429,13007432013,12940458317,4350392669,4350525789], by decide +kernel⟩,⟨Compact54Packed.unpack [4400720237,4400918893,4350589293,4317102445,22069621,22136181], by decide +kernel⟩,⟨Compact54Packed.unpack [38779261,38911357,38977917,5424509,5424512,5424516], by decide +kernel⟩,⟨Compact54Packed.unpack [34616130953,17435943305,13141308809,17302521225,12940515721,4350585225], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [4317098377,22133129,5422473,22200712,5422476], by decide +kernel⟩,⟨Compact54Packed.unpack [22200716,22000017,22132113,5421457,5422480], by decide +kernel⟩,⟨Compact54Packed.unpack [22200720,55753108], by decide +kernel⟩,⟨Compact54Packed.unpack [4350319001,4350517657,4317096345,22131097,5420441,5421464], by decide +kernel⟩,⟨Compact54Packed.unpack [38976920,38974876], by decide +kernel⟩,⟨Compact54Packed.unpack [22200732,21997985,22130081,5419425,5420448], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [55753120,22196644], by decide +kernel⟩,⟨Compact54Packed.unpack [55753124,8712390057,4417556905], by decide +kernel⟩,⟨Compact54Packed.unpack [4350515625,4317094313,22129065,5352872,22196648], by decide +kernel⟩,⟨Compact54Packed.unpack [55753128,5352876,5419436], by decide +kernel⟩,⟨Compact54Packed.unpack [72529324,21995953], by decide +kernel⟩,⟨Compact54Packed.unpack [22062513,5351857,5352880,38973872], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [38976944,22129076,5419444], by decide +kernel⟩,⟨Compact54Packed.unpack [72529332,4317026745], by decide +kernel⟩,⟨Compact54Packed.unpack [22061497,5350841,22129080,22196664], by decide +kernel⟩,⟨Compact54Packed.unpack [55753144,22128060], by decide +kernel⟩,⟨Compact54Packed.unpack [5352892,72528316], by decide +kernel⟩,⟨Compact54Packed.unpack [5424572,21928385,21994945,22127041,22128064], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [89304512], by decide +kernel⟩,⟨Compact54Packed.unpack [5424576,22128068,38972868], by decide +kernel⟩,⟨Compact54Packed.unpack [55753156,17418304969,13123801545], by decide +kernel⟩,⟨Compact54Packed.unpack [17419755977,13007418825,8645477833,4350579145,21993929,22126025], by decide +kernel⟩,⟨Compact54Packed.unpack [38904264,38972872], by decide +kernel⟩,⟨Compact54Packed.unpack [55753160,22127052], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5351884,72527308], by decide +kernel⟩,⟨Compact54Packed.unpack [22200780,22059473,38903248], by decide +kernel⟩,⟨Compact54Packed.unpack [5351888,72527312], by decide +kernel⟩,⟨Compact54Packed.unpack [22200784,55680468], by decide +kernel⟩,⟨Compact54Packed.unpack [89304532], by decide +kernel⟩,⟨Compact54Packed.unpack [5424596,8645608921,21860825,22058457,5347801,5348824], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [38904280,38972888], by decide +kernel⟩,⟨Compact54Packed.unpack [55753176,22125020], by decide +kernel⟩,⟨Compact54Packed.unpack [38904284,38972892], by decide +kernel⟩,⟨Compact54Packed.unpack [55753180,21991905,22124001], by decide +kernel⟩,⟨Compact54Packed.unpack [72456672,5418464], by decide +kernel⟩,⟨Compact54Packed.unpack [89305568], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [55679460,22194660], by decide +kernel⟩,⟨Compact54Packed.unpack [89305572], by decide +kernel⟩,⟨Compact54Packed.unpack [4400379369,4400643561,4350510569,55545321,22057449,5346792], by decide +kernel⟩,⟨Compact54Packed.unpack [55679464,22194664], by decide +kernel⟩,⟨Compact54Packed.unpack [89305576], by decide +kernel⟩,⟨Compact54Packed.unpack [72455660,5417452], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [89304556], by decide +kernel⟩,⟨Compact54Packed.unpack [5424620,22122993,55678448], by decide +kernel⟩,⟨Compact54Packed.unpack [5350896,72526320], by decide +kernel⟩,⟨Compact54Packed.unpack [38977008,38901236], by decide +kernel⟩,⟨Compact54Packed.unpack [22127092,55749108], by decide +kernel⟩,⟨Compact54Packed.unpack [55753204,4333864441,38899193], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [89231864], by decide +kernel⟩,⟨Compact54Packed.unpack [89303544], by decide +kernel⟩,⟨Compact54Packed.unpack [22200824,55677436], by decide +kernel⟩,⟨Compact54Packed.unpack [22127100,55749116], by decide +kernel⟩,⟨Compact54Packed.unpack [55753212,22123008], by decide +kernel⟩,⟨Compact54Packed.unpack [55679488,22194688], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [89305600], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 128 15 8 = true := by decide +kernel
private theorem i23 : checks ts 128 23 8 = true := by decide +kernel
private theorem i31 : checks ts 128 31 8 = true := by decide +kernel
private theorem i39 : checks ts 128 39 8 = true := by decide +kernel
private theorem i47 : checks ts 128 47 3 = true := by decide +kernel
private theorem rows : checks ts 128 15 35 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 7 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6thinwide 6
private def p0 : List P := [⟨Compact54Packed.unpack [64930596889,64881657905,30570858645,30571522197,30521788577,30522321057], by decide +kernel⟩,⟨Compact54Packed.unpack [30572103953,30573029649,30321379601,30187301137,13007104305,13007501617], by decide +kernel⟩,⟨Compact54Packed.unpack [13124536657,13124999505,13007563089,12940589393,4350523745,4350722401], by decide +kernel⟩,⟨Compact54Packed.unpack [4400785777,4400984433,4350720369,22069617,22201713,22200697], by decide +kernel⟩,⟨Compact54Packed.unpack [5424505,5424508,38910337,22199681,22200704], by decide +kernel⟩,⟨Compact54Packed.unpack [22200708,38976904,30304258445], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [13124135309,13124663693,13007423885,4350187917,4350452109,4350650765], by decide +kernel⟩,⟨Compact54Packed.unpack [22000013,22132109,5421453,38976908], by decide +kernel⟩,⟨Compact54Packed.unpack [55753104,22131093,5420437], by decide +kernel⟩,⟨Compact54Packed.unpack [55753108,22197656], by decide +kernel⟩,⟨Compact54Packed.unpack [38976920,4350384541,4350648733,21997981], by decide +kernel⟩,⟨Compact54Packed.unpack [22130077,22196637,55752092], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [5424540,72529312], by decide +kernel⟩,⟨Compact54Packed.unpack [22063525,5352869,55751076], by decide +kernel⟩,⟨Compact54Packed.unpack [22200740,5352872,38973864], by decide +kernel⟩,⟨Compact54Packed.unpack [38976936,4400515501,4400779693,4350581165], by decide +kernel⟩,⟨Compact54Packed.unpack [21930413,22062509,5351853,5352876,22196652], by decide +kernel⟩,⟨Compact54Packed.unpack [55753132,22129072], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [89305520], by decide +kernel⟩,⟨Compact54Packed.unpack [22061493,22128053,22129076,22196660], by decide +kernel⟩,⟨Compact54Packed.unpack [55753140,22129080], by decide +kernel⟩,⟨Compact54Packed.unpack [89305528], by decide +kernel⟩,⟨Compact54Packed.unpack [38705597,38837693,22127037,38905276], by decide +kernel⟩,⟨Compact54Packed.unpack [89305532], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [22128064,55750080], by decide +kernel⟩,⟨Compact54Packed.unpack [38976960,38904260], by decide +kernel⟩,⟨Compact54Packed.unpack [89304516], by decide +kernel⟩,⟨Compact54Packed.unpack [5424580,13123406281,13124065737,13124659657,13007550921,4350314953], by decide +kernel⟩,⟨Compact54Packed.unpack [4350579145,21993929,22126025,38904264], by decide +kernel⟩,⟨Compact54Packed.unpack [89304520], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5424584,38904268,22195660], by decide +kernel⟩,⟨Compact54Packed.unpack [72529356,22059473], by decide +kernel⟩,⟨Compact54Packed.unpack [55680464,22195664], by decide +kernel⟩,⟨Compact54Packed.unpack [72529360,5348820], by decide +kernel⟩,⟨Compact54Packed.unpack [38904276,38972884], by decide +kernel⟩,⟨Compact54Packed.unpack [55753172,4350511577,21860825], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [22058457,5347801,55680472], by decide +kernel⟩,⟨Compact54Packed.unpack [89304536], by decide +kernel⟩,⟨Compact54Packed.unpack [5424600,72456668], by decide +kernel⟩,⟨Compact54Packed.unpack [89304540], by decide +kernel⟩,⟨Compact54Packed.unpack [5424604,21991905,22124001,38902240], by decide +kernel⟩,⟨Compact54Packed.unpack [22128096,55750112], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [38976992,38902244], by decide +kernel⟩,⟨Compact54Packed.unpack [5350884,72526308], by decide +kernel⟩,⟨Compact54Packed.unpack [38976996,4400511465,4400841193,4350642665], by decide +kernel⟩,⟨Compact54Packed.unpack [22057449,72455656], by decide +kernel⟩,⟨Compact54Packed.unpack [89303528], by decide +kernel⟩,⟨Compact54Packed.unpack [22200808,55678444], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [5350892,72526316], by decide +kernel⟩,⟨Compact54Packed.unpack [38977004,22122993,22124016], by decide +kernel⟩,⟨Compact54Packed.unpack [38903280,38971888], by decide +kernel⟩,⟨Compact54Packed.unpack [72529392,5346804], by decide +kernel⟩,⟨Compact54Packed.unpack [55679476,22194676], by decide +kernel⟩,⟨Compact54Packed.unpack [89305588], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [38701561,38899193,55677432], by decide +kernel⟩,⟨Compact54Packed.unpack [22127096,55749112], by decide +kernel⟩,⟨Compact54Packed.unpack [55753208,22123004], by decide +kernel⟩,⟨Compact54Packed.unpack [55679484,22194684], by decide +kernel⟩,⟨Compact54Packed.unpack [89305596], by decide +kernel⟩,⟨Compact54Packed.unpack [89231872], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [89303552], by decide +kernel⟩,⟨Compact54Packed.unpack [22200832], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 128 18 8 = true := by decide +kernel
private theorem i26 : checks ts 128 26 8 = true := by decide +kernel
private theorem i34 : checks ts 128 34 8 = true := by decide +kernel
private theorem i42 : checks ts 128 42 8 = true := by decide +kernel
private theorem rows : checks ts 128 18 32 = true := checks_join i18 (checks_join i26 (checks_join i34 (i42)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 8 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

end Compact50PriceTableTwo6thinwide
