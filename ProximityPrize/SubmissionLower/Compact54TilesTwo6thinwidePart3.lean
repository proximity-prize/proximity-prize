import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo6thinwidePart2

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top9
private abbrev P := PaidBatch .two6thinwide 9
private def p0 : List P := [⟨Compact54Packed.unpack [47733828645,43372944437,47735598237,43441364125,21713415445,21714076949], by decide +kernel⟩,⟨Compact54Packed.unpack [21714738453,17420104981,21714070865,21714797905,8712068433,8712464721], by decide +kernel⟩,⟨Compact54Packed.unpack [8645424465,4350591313,4350457185,55491937,4317102433,22069609], by decide +kernel⟩,⟨Compact54Packed.unpack [22136169,8695618929,8645552497,4350653809,55688561,22135153], by decide +kernel⟩,⟨Compact54Packed.unpack [5424497,5424500,5423481,5424504,22200700], by decide +kernel⟩,⟨Compact54Packed.unpack [4333676929,38711681,38843777,38975873,5422465,5423488], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [5424512,38976900,22199688], by decide +kernel⟩,⟨Compact54Packed.unpack [5424520,21714726285,8711996813,8712393101,8645483917,4350650765], by decide +kernel⟩,⟨Compact54Packed.unpack [55685517,22197645,55753100], by decide +kernel⟩,⟨Compact54Packed.unpack [55753104,5420437,5421460], by decide +kernel⟩,⟨Compact54Packed.unpack [38976916,38974872], by decide +kernel⟩,⟨Compact54Packed.unpack [22200728,4350451101,55485853,21997981,22130077], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [5419421,72529308], by decide +kernel⟩,⟨Compact54Packed.unpack [89305504], by decide +kernel⟩,⟨Compact54Packed.unpack [22063525,5352868,55751076], by decide +kernel⟩,⟨Compact54Packed.unpack [22200740,5352872,38973864], by decide +kernel⟩,⟨Compact54Packed.unpack [38976936,8695547309,8695943597,4350647725], by decide +kernel⟩,⟨Compact54Packed.unpack [55682477,5351853,5352876,38973868], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [38976940,22129072,5419440], by decide +kernel⟩,⟨Compact54Packed.unpack [72529328,5351860], by decide +kernel⟩,⟨Compact54Packed.unpack [5352884,72528308], by decide +kernel⟩,⟨Compact54Packed.unpack [5424564,22129080,38973880], by decide +kernel⟩,⟨Compact54Packed.unpack [38976952,38772157,38904253,5350844], by decide +kernel⟩,⟨Compact54Packed.unpack [22129084,55751100], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [22200764,22128064,22195648], by decide +kernel⟩,⟨Compact54Packed.unpack [72529344,5350852], by decide +kernel⟩,⟨Compact54Packed.unpack [5351876,72527300], by decide +kernel⟩,⟨Compact54Packed.unpack [22200772,8711728585,8712190409,8712652233,4350513609], by decide +kernel⟩,⟨Compact54Packed.unpack [55548361,22060489,38904264,5418440], by decide +kernel⟩,⟨Compact54Packed.unpack [89305544], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [38904268,38972876], by decide +kernel⟩,⟨Compact54Packed.unpack [55753164,5348817,5349840], by decide +kernel⟩,⟨Compact54Packed.unpack [22128080,55750096], by decide +kernel⟩,⟨Compact54Packed.unpack [38976976,38903252], by decide +kernel⟩,⟨Compact54Packed.unpack [5351892,72527316], by decide +kernel⟩,⟨Compact54Packed.unpack [22200788,4317090265,22125017,22126040], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [22128088,55750104], by decide +kernel⟩,⟨Compact54Packed.unpack [38976984,38903260], by decide +kernel⟩,⟨Compact54Packed.unpack [5351900,72527324], by decide +kernel⟩,⟨Compact54Packed.unpack [22200796,21860833,22058465,5347809,5348832], by decide +kernel⟩,⟨Compact54Packed.unpack [38904288,38972896], by decide +kernel⟩,⟨Compact54Packed.unpack [55753184,22125028], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [22127076,55749092], by decide +kernel⟩,⟨Compact54Packed.unpack [55753188,8695213545,8695675369], by decide +kernel⟩,⟨Compact54Packed.unpack [4350379497,55414249,21991913,22124009,22125032], by decide +kernel⟩,⟨Compact54Packed.unpack [22127080,55749096], by decide +kernel⟩,⟨Compact54Packed.unpack [55753192,22125036], by decide +kernel⟩,⟨Compact54Packed.unpack [22127084,55749100], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [55753196,22057457,5346800], by decide +kernel⟩,⟨Compact54Packed.unpack [55679472,22194672], by decide +kernel⟩,⟨Compact54Packed.unpack [89305584], by decide +kernel⟩,⟨Compact54Packed.unpack [72455668,5417460], by decide +kernel⟩,⟨Compact54Packed.unpack [89304564], by decide +kernel⟩,⟨Compact54Packed.unpack [5424628,4333733369,38768121,22123001,22124024], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [38903288,38971896], by decide +kernel⟩,⟨Compact54Packed.unpack [72529400,5346812], by decide +kernel⟩,⟨Compact54Packed.unpack [55679484,22194684], by decide +kernel⟩,⟨Compact54Packed.unpack [89305596], by decide +kernel⟩,⟨Compact54Packed.unpack [89231872], by decide +kernel⟩,⟨Compact54Packed.unpack [89303552], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [22200832], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 128 27 8 = true := by decide +kernel
private theorem i35 : checks ts 128 35 8 = true := by decide +kernel
private theorem i43 : checks ts 128 43 7 = true := by decide +kernel
private theorem rows : checks ts 128 27 23 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 11 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6thinwide 10
private def p0 : List P := [⟨Compact54Packed.unpack [82095994921,39145535649,39146397857,38894729497,17419641113,17302336793], by decide +kernel⟩,⟨Compact54Packed.unpack [8695625017,4400726329,17419237717,17419832661,17302659413,8645490005], by decide +kernel⟩,⟨Compact54Packed.unpack [4350656853,4350522725,55557477,4317167973,22135149,22201709], by decide +kernel⟩,⟨Compact54Packed.unpack [8695816565,4400983413,4350719349,55754101,22200693,5424500], by decide +kernel⟩,⟨Compact54Packed.unpack [5424504,22200700,22200704,38909317], by decide +kernel⟩,⟨Compact54Packed.unpack [22198661,38976900,22199688], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [5424520,55753100,17419827601], by decide +kernel⟩,⟨Compact54Packed.unpack [8712261009,4417493393,4350452113,55486865,21933457,22065553], by decide +kernel⟩,⟨Compact54Packed.unpack [22197649,55753104,5421460], by decide +kernel⟩,⟨Compact54Packed.unpack [38976916,22064537,5353881,5420440], by decide +kernel⟩,⟨Compact54Packed.unpack [55753112,5419421,5420444], by decide +kernel⟩,⟨Compact54Packed.unpack [55753116,4350648737,55683489], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [22130081,72528288], by decide +kernel⟩,⟨Compact54Packed.unpack [5424544,72528292], by decide +kernel⟩,⟨Compact54Packed.unpack [5424548,5352872,55751080], by decide +kernel⟩,⟨Compact54Packed.unpack [22200744,5352876,38973868], by decide +kernel⟩,⟨Compact54Packed.unpack [38976940,8695811505,4400978353,21930417], by decide +kernel⟩,⟨Compact54Packed.unpack [22062513,5351857,5352880,38973872], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [38976944,22129076,5419444], by decide +kernel⟩,⟨Compact54Packed.unpack [72529332,21995961], by decide +kernel⟩,⟨Compact54Packed.unpack [22128057,22129080,38973880], by decide +kernel⟩,⟨Compact54Packed.unpack [38976952,22129084,5419452], by decide +kernel⟩,⟨Compact54Packed.unpack [72529340,38904257], by decide +kernel⟩,⟨Compact54Packed.unpack [22128064,55750080], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [38976960,22128068,5418436], by decide +kernel⟩,⟨Compact54Packed.unpack [89305540], by decide +kernel⟩,⟨Compact54Packed.unpack [22128072,55750088], by decide +kernel⟩,⟨Compact54Packed.unpack [38976968,8695347661,4400514509,4350381517], by decide +kernel⟩,⟨Compact54Packed.unpack [55416269,21928397,22060493,38904268], by decide +kernel⟩,⟨Compact54Packed.unpack [89304524], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5424588,38904272,22195664], by decide +kernel⟩,⟨Compact54Packed.unpack [72529360,22059477], by decide +kernel⟩,⟨Compact54Packed.unpack [5348821,38904276,22195668], by decide +kernel⟩,⟨Compact54Packed.unpack [72529364,5348824], by decide +kernel⟩,⟨Compact54Packed.unpack [38904280,38972888], by decide +kernel⟩,⟨Compact54Packed.unpack [55753176,4333735389,38770141], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [22125021,55680476,5418460], by decide +kernel⟩,⟨Compact54Packed.unpack [89305564], by decide +kernel⟩,⟨Compact54Packed.unpack [55680480,22195680], by decide +kernel⟩,⟨Compact54Packed.unpack [72529376,5347812], by decide +kernel⟩,⟨Compact54Packed.unpack [38903268,38971876], by decide +kernel⟩,⟨Compact54Packed.unpack [72529380,8695609833], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [4400842217,4317023721,22058473,38902248], by decide +kernel⟩,⟨Compact54Packed.unpack [5350888,72526312], by decide +kernel⟩,⟨Compact54Packed.unpack [38977000,38902252], by decide +kernel⟩,⟨Compact54Packed.unpack [5350892,72526316], by decide +kernel⟩,⟨Compact54Packed.unpack [38977004,21859825,21991921,5346801], by decide +kernel⟩,⟨Compact54Packed.unpack [55679472,22194672], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [89305584], by decide +kernel⟩,⟨Compact54Packed.unpack [72455668,5417460], by decide +kernel⟩,⟨Compact54Packed.unpack [89304564], by decide +kernel⟩,⟨Compact54Packed.unpack [5424628,38768121,38900217,38901240], by decide +kernel⟩,⟨Compact54Packed.unpack [22127096,55749112], by decide +kernel⟩,⟨Compact54Packed.unpack [55753208,22124028], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [38903292,38971900], by decide +kernel⟩,⟨Compact54Packed.unpack [72529404,5346816], by decide +kernel⟩,⟨Compact54Packed.unpack [55679488,22194688], by decide +kernel⟩,⟨Compact54Packed.unpack [89305600], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 128 30 8 = true := by decide +kernel
private theorem i38 : checks ts 128 38 8 = true := by decide +kernel
private theorem i46 : checks ts 128 46 4 = true := by decide +kernel
private theorem rows : checks ts 128 30 20 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 12 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6thinwide 11
private def p0 : List P := [⟨Compact54Packed.unpack [69210637357,34833794213,30539425957,34599765273,13124675865,13125138713], by decide +kernel⟩,⟨Compact54Packed.unpack [17419568469,13124999509,13007694165,4350392661,4350656853,4350589285], by decide +kernel⟩,⟨Compact54Packed.unpack [4317167973,22135149,22201709,4400785781,4350587253,4317165941], by decide +kernel⟩,⟨Compact54Packed.unpack [22200693,5424500,5424504,22067581,22199677,5423484], by decide +kernel⟩,⟨Compact54Packed.unpack [5424508,22200704,38777221,38843781,38975877], by decide +kernel⟩,⟨Compact54Packed.unpack [38976900,38976904], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [38976908,17302521233,4350122385,4350386577], by decide +kernel⟩,⟨Compact54Packed.unpack [4350650769,22065553,22197649,38975888], by decide +kernel⟩,⟨Compact54Packed.unpack [5424528,55753108,5353881], by decide +kernel⟩,⟨Compact54Packed.unpack [72529304,5419421], by decide +kernel⟩,⟨Compact54Packed.unpack [72529308,4350319009], by decide +kernel⟩,⟨Compact54Packed.unpack [4350583201,21997985,22130081,5419425,22197664], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [38976928,38973860], by decide +kernel⟩,⟨Compact54Packed.unpack [38976932,22063529,5352872,5419432], by decide +kernel⟩,⟨Compact54Packed.unpack [72529320,5352876], by decide +kernel⟩,⟨Compact54Packed.unpack [89305516], by decide +kernel⟩,⟨Compact54Packed.unpack [8695481777,4400648625,4400978353,21864881,22062513,5351857], by decide +kernel⟩,⟨Compact54Packed.unpack [5352880,72528304], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [5424560,22129076,38973876], by decide +kernel⟩,⟨Compact54Packed.unpack [38976948,21995961,22128057,5351864], by decide +kernel⟩,⟨Compact54Packed.unpack [5352888,72528312], by decide +kernel⟩,⟨Compact54Packed.unpack [5424568,22129084,38973884], by decide +kernel⟩,⟨Compact54Packed.unpack [38976956,38904257,22128064], by decide +kernel⟩,⟨Compact54Packed.unpack [89304512], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [5424576,22128068,38972868], by decide +kernel⟩,⟨Compact54Packed.unpack [55753156,22128072], by decide +kernel⟩,⟨Compact54Packed.unpack [89304520], by decide +kernel⟩,⟨Compact54Packed.unpack [5424584,8695809485,4400976333,21928397,22060493,5349836], by decide +kernel⟩,⟨Compact54Packed.unpack [22128076,55750092], by decide +kernel⟩,⟨Compact54Packed.unpack [38976972,38904272], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [89304528], by decide +kernel⟩,⟨Compact54Packed.unpack [5424592,21993941,22126037,38904276], by decide +kernel⟩,⟨Compact54Packed.unpack [89304532], by decide +kernel⟩,⟨Compact54Packed.unpack [5424596,38904280,22195672], by decide +kernel⟩,⟨Compact54Packed.unpack [72529368,38902237], by decide +kernel⟩,⟨Compact54Packed.unpack [55680476,22195676], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [72529372,5348832], by decide +kernel⟩,⟨Compact54Packed.unpack [38904288,38972896], by decide +kernel⟩,⟨Compact54Packed.unpack [55753184,22126052], by decide +kernel⟩,⟨Compact54Packed.unpack [5350884,72526308], by decide +kernel⟩,⟨Compact54Packed.unpack [38976996,8645608937,21926377,22058473], by decide +kernel⟩,⟨Compact54Packed.unpack [55679464,22194664], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [89305576], by decide +kernel⟩,⟨Compact54Packed.unpack [55679468,22194668], by decide +kernel⟩,⟨Compact54Packed.unpack [89305580], by decide +kernel⟩,⟨Compact54Packed.unpack [21991921,22124017,55679472], by decide +kernel⟩,⟨Compact54Packed.unpack [89303536], by decide +kernel⟩,⟨Compact54Packed.unpack [22200816,55679476], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [89303540], by decide +kernel⟩,⟨Compact54Packed.unpack [22200820,4333667833,38702585,38900217,5346808], by decide +kernel⟩,⟨Compact54Packed.unpack [55679480,22194680], by decide +kernel⟩,⟨Compact54Packed.unpack [89305592], by decide +kernel⟩,⟨Compact54Packed.unpack [72455676,5417468], by decide +kernel⟩,⟨Compact54Packed.unpack [89304572], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [5424636,72455680], by decide +kernel⟩,⟨Compact54Packed.unpack [89303552], by decide +kernel⟩,⟨Compact54Packed.unpack [22200832], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 128 33 8 = true := by decide +kernel
private theorem i41 : checks ts 128 41 8 = true := by decide +kernel
private theorem i49 : checks ts 128 49 1 = true := by decide +kernel
private theorem rows : checks ts 128 33 17 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 13 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

end Compact50PriceTableTwo6thinwide
