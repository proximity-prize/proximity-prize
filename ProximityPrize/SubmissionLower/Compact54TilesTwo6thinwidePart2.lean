import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo6thinwidePart1

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top7
private abbrev P := PaidBatch .two6thinwide 7
private def p0 : List P := [⟨Compact54Packed.unpack [60635632669,56258039857,60620887193,56073752729,26008719573,26009251029], by decide +kernel⟩,⟨Compact54Packed.unpack [30320121105,26025686289,26026414353,25892269329,13007236401,8712469809], by decide +kernel⟩,⟨Compact54Packed.unpack [30303999313,26009630033,13006967121,8712200529,13007695185,8645623121], by decide +kernel⟩,⟨Compact54Packed.unpack [4350655841,55690593,12990517617,8695816561,4400917873,4350653809], by decide +kernel⟩,⟨Compact54Packed.unpack [22003057,22135153,22201713,22134137,22200697,5424504], by decide +kernel⟩,⟨Compact54Packed.unpack [5424508,38843777,38975873,22199681,22200704], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [22200708,38976904,30304589197], by decide +kernel⟩,⟨Compact54Packed.unpack [13006763405,8712062349,13007688077,4350452109,55486861,21933453], by decide +kernel⟩,⟨Compact54Packed.unpack [22065549,22132109,5421453,38976908], by decide +kernel⟩,⟨Compact54Packed.unpack [55753104,21998997,22131093], by decide +kernel⟩,⟨Compact54Packed.unpack [5420437,55753108,5420440], by decide +kernel⟩,⟨Compact54Packed.unpack [55753112,4350648733,55683485], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [22130077,5419421,55752092], by decide +kernel⟩,⟨Compact54Packed.unpack [5424540,72528288], by decide +kernel⟩,⟨Compact54Packed.unpack [5424544,5352868,55751076], by decide +kernel⟩,⟨Compact54Packed.unpack [22200740,5352872,38973864], by decide +kernel⟩,⟨Compact54Packed.unpack [38976936,12990313901,8695612845,4400779693], by decide +kernel⟩,⟨Compact54Packed.unpack [4350581165,21930413,22062509,5351853,5352876,5419436], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [72529324,5351856], by decide +kernel⟩,⟨Compact54Packed.unpack [5352880,72528304], by decide +kernel⟩,⟨Compact54Packed.unpack [5424560,22061493,5350837,22129076,5419444], by decide +kernel⟩,⟨Compact54Packed.unpack [72529332,5350840], by decide +kernel⟩,⟨Compact54Packed.unpack [22129080,55751096], by decide +kernel⟩,⟨Compact54Packed.unpack [22200760,38705597,38837693,22127037,5350844], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [22129084,55751100], by decide +kernel⟩,⟨Compact54Packed.unpack [22200764,22128064,22195648], by decide +kernel⟩,⟨Compact54Packed.unpack [72529344,5349828], by decide +kernel⟩,⟨Compact54Packed.unpack [22128068,55750084], by decide +kernel⟩,⟨Compact54Packed.unpack [38976964,13123868105,13124462025,13007418825], by decide +kernel⟩,⟨Compact54Packed.unpack [8645412297,4350579145,21993929,22126025,22127048], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5351880,72527304], by decide +kernel⟩,⟨Compact54Packed.unpack [22200776,38904268,5418444], by decide +kernel⟩,⟨Compact54Packed.unpack [89305548], by decide +kernel⟩,⟨Compact54Packed.unpack [22059473,55680464,5418448], by decide +kernel⟩,⟨Compact54Packed.unpack [89305552], by decide +kernel⟩,⟨Compact54Packed.unpack [55680468,22195668], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [72529364,8645608921], by decide +kernel⟩,⟨Compact54Packed.unpack [21860825,21992921,5347801,38903256], by decide +kernel⟩,⟨Compact54Packed.unpack [5351896,72527320], by decide +kernel⟩,⟨Compact54Packed.unpack [22200792,55679452], by decide +kernel⟩,⟨Compact54Packed.unpack [5351900,72527324], by decide +kernel⟩,⟨Compact54Packed.unpack [22200796,21926369,22124001,22125024], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [38904288,38972896], by decide +kernel⟩,⟨Compact54Packed.unpack [55753184,22125028], by decide +kernel⟩,⟨Compact54Packed.unpack [22127076,55749092], by decide +kernel⟩,⟨Compact54Packed.unpack [55753188,4400313833,4400643561], by decide +kernel⟩,⟨Compact54Packed.unpack [4350510569,55545321,22057449,5346793,22125032], by decide +kernel⟩,⟨Compact54Packed.unpack [22127080,55749096], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [55753192,22124012], by decide +kernel⟩,⟨Compact54Packed.unpack [38903276,38971884], by decide +kernel⟩,⟨Compact54Packed.unpack [72529388,22122993], by decide +kernel⟩,⟨Compact54Packed.unpack [72455664,5417456], by decide +kernel⟩,⟨Compact54Packed.unpack [89304560], by decide +kernel⟩,⟨Compact54Packed.unpack [5424624,72455668], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [89303540], by decide +kernel⟩,⟨Compact54Packed.unpack [22200820,4333798905,38833657,22123000], by decide +kernel⟩,⟨Compact54Packed.unpack [55679480,22194680], by decide +kernel⟩,⟨Compact54Packed.unpack [89305592], by decide +kernel⟩,⟨Compact54Packed.unpack [89231868], by decide +kernel⟩,⟨Compact54Packed.unpack [89303548], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [22200828,55677440], by decide +kernel⟩,⟨Compact54Packed.unpack [22127104,55749120], by decide +kernel⟩,⟨Compact54Packed.unpack [55753216], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 128 21 8 = true := by decide +kernel
private theorem i29 : checks ts 128 29 8 = true := by decide +kernel
private theorem i37 : checks ts 128 37 8 = true := by decide +kernel
private theorem i45 : checks ts 128 45 5 = true := by decide +kernel
private theorem rows : checks ts 128 21 29 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 9 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two6thinwide 8
private def p0 : List P := [⟨Compact54Packed.unpack [52045570081,51963073589,52030627997,51778786461,26008851673,21714284761], by decide +kernel⟩,⟨Compact54Packed.unpack [26008379669,21713878293,26009703701,21597303061,8695427381,8695758133], by decide +kernel⟩,⟨Compact54Packed.unpack [26009035089,21714599249,13007099217,8712332625,8712663377,8645623121], by decide +kernel⟩,⟨Compact54Packed.unpack [4350655841,55690593,12990649713,8695883121,4350587249,55556465], by decide +kernel⟩,⟨Compact54Packed.unpack [22068593,22135153,5424497,5424500,22134137,5423481], by decide +kernel⟩,⟨Compact54Packed.unpack [5424504,22200700,38711681,38843777,38975873], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [5422465,22200704,38976900], by decide +kernel⟩,⟨Compact54Packed.unpack [38976904,26009624973,21597552013,12940514701], by decide +kernel⟩,⟨Compact54Packed.unpack [4350584205,55618957,22065549,22197645,22198668], by decide +kernel⟩,⟨Compact54Packed.unpack [22200716,55753104], by decide +kernel⟩,⟨Compact54Packed.unpack [22131093,5420437,55753108], by decide +kernel⟩,⟨Compact54Packed.unpack [72529304,4350252445], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [4350516637,4317095325,22130077,5419421,22197660], by decide +kernel⟩,⟨Compact54Packed.unpack [38976924,38973856], by decide +kernel⟩,⟨Compact54Packed.unpack [38976928,21996965,22129061,5352868], by decide +kernel⟩,⟨Compact54Packed.unpack [89305508], by decide +kernel⟩,⟨Compact54Packed.unpack [5352872,72528296], by decide +kernel⟩,⟨Compact54Packed.unpack [5424552,8695283117,8695679405,4400846253,4350647725,22062509], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [5351853,5352876,55751084], by decide +kernel⟩,⟨Compact54Packed.unpack [22200748,22129072,22196656], by decide +kernel⟩,⟨Compact54Packed.unpack [55753136,22128053,5351860], by decide +kernel⟩,⟨Compact54Packed.unpack [5352884,72528308], by decide +kernel⟩,⟨Compact54Packed.unpack [5424564,22129080,38973880], by decide +kernel⟩,⟨Compact54Packed.unpack [38976952,38772157,38904253,5350844], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [22129084,55751100], by decide +kernel⟩,⟨Compact54Packed.unpack [22200764,22128064,22195648], by decide +kernel⟩,⟨Compact54Packed.unpack [72529344,5350852], by decide +kernel⟩,⟨Compact54Packed.unpack [5351876,72527300], by decide +kernel⟩,⟨Compact54Packed.unpack [22200772,13006561737,8711926217,8712388041,8645544393], by decide +kernel⟩,⟨Compact54Packed.unpack [4317091273,22126025,38904264,5418440], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [89305544], by decide +kernel⟩,⟨Compact54Packed.unpack [38904268,38972876], by decide +kernel⟩,⟨Compact54Packed.unpack [55753164,21927377,22059473], by decide +kernel⟩,⟨Compact54Packed.unpack [5348817,38904272,22195664], by decide +kernel⟩,⟨Compact54Packed.unpack [72529360,5348820], by decide +kernel⟩,⟨Compact54Packed.unpack [38904276,38972884], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [55753172,4350446041,55480793], by decide +kernel⟩,⟨Compact54Packed.unpack [21992921,22125017,55680472], by decide +kernel⟩,⟨Compact54Packed.unpack [89304536], by decide +kernel⟩,⟨Compact54Packed.unpack [5424600,55680476,5418460], by decide +kernel⟩,⟨Compact54Packed.unpack [89305564], by decide +kernel⟩,⟨Compact54Packed.unpack [22058465,72456672], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [89304544], by decide +kernel⟩,⟨Compact54Packed.unpack [5424608,55679460,5417444], by decide +kernel⟩,⟨Compact54Packed.unpack [89304548], by decide +kernel⟩,⟨Compact54Packed.unpack [5424612,12990046697,8695411177,8695873001,4350577129,55611881], by decide +kernel⟩,⟨Compact54Packed.unpack [5346793,55679464,5417448], by decide +kernel⟩,⟨Compact54Packed.unpack [89304552], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [5424616,72455660], by decide +kernel⟩,⟨Compact54Packed.unpack [89303532], by decide +kernel⟩,⟨Compact54Packed.unpack [22200812,55678448], by decide +kernel⟩,⟨Compact54Packed.unpack [5350896,72526320], by decide +kernel⟩,⟨Compact54Packed.unpack [38977008,38901236], by decide +kernel⟩,⟨Compact54Packed.unpack [22127092,55749108], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [55753204,38636025,38833657], by decide +kernel⟩,⟨Compact54Packed.unpack [5345785,72455672], by decide +kernel⟩,⟨Compact54Packed.unpack [89303544], by decide +kernel⟩,⟨Compact54Packed.unpack [22200824,55677436], by decide +kernel⟩,⟨Compact54Packed.unpack [22127100,55749116], by decide +kernel⟩,⟨Compact54Packed.unpack [55753212,22123008], by decide +kernel⟩]
private def p10 : List P := [⟨Compact54Packed.unpack [55679488,22194688], by decide +kernel⟩,⟨Compact54Packed.unpack [89305600], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9 ++ p10
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 128 24 8 = true := by decide +kernel
private theorem i32 : checks ts 128 32 8 = true := by decide +kernel
private theorem i40 : checks ts 128 40 8 = true := by decide +kernel
private theorem i48 : checks ts 128 48 2 = true := by decide +kernel
private theorem rows : checks ts 128 24 26 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 10 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

end Compact50PriceTableTwo6thinwide
