import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesTwo6thinwidePart3

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top12
private abbrev P := PaidBatch .two6thinwide 12
private def p0 : List P := [⟨Compact54Packed.unpack [56325345329,56074211497,25992073445,25992735973,26009637149,25892597021], by decide +kernel⟩,⟨Compact54Packed.unpack [12990590269,8695889213,12990124377,8695423321,4400590169,4400788825], by decide +kernel⟩,⟨Compact54Packed.unpack [4350590297,55625049,4333944169,38978921,12990452085,8695751029], by decide +kernel⟩,⟨Compact54Packed.unpack [4400917877,4350719349,22068597,22200693,5424500,5424504], by decide +kernel⟩,⟨Compact54Packed.unpack [22199677,22200700,22200704,38843781], by decide +kernel⟩,⟨Compact54Packed.unpack [38975877,5422469,22200708,22199688], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [5424520,38976908,13007622545,8645616017], by decide +kernel⟩,⟨Compact54Packed.unpack [21933457,22065553,22197649,38975888], by decide +kernel⟩,⟨Compact54Packed.unpack [5424528,55753108,21999001], by decide +kernel⟩,⟨Compact54Packed.unpack [22131097,5420441,55753112], by decide +kernel⟩,⟨Compact54Packed.unpack [72529308,4350583201], by decide +kernel⟩,⟨Compact54Packed.unpack [55617953,22130081,5419425,38974880], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [22200736,55751076], by decide +kernel⟩,⟨Compact54Packed.unpack [22200740,5352873,38973864], by decide +kernel⟩,⟨Compact54Packed.unpack [38976936,5352876,22196652], by decide +kernel⟩,⟨Compact54Packed.unpack [55753132,4400648625,4400912817], by decide +kernel⟩,⟨Compact54Packed.unpack [4317094321,22129073,5352880,38973872], by decide +kernel⟩,⟨Compact54Packed.unpack [38976944,5352884,22196660], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [55753140,21930425,22128057], by decide +kernel⟩,⟨Compact54Packed.unpack [22129080,55751096], by decide +kernel⟩,⟨Compact54Packed.unpack [22200760,22129084,22196668], by decide +kernel⟩,⟨Compact54Packed.unpack [55753148,38838721,5350849], by decide +kernel⟩,⟨Compact54Packed.unpack [5351872,72527296], by decide +kernel⟩,⟨Compact54Packed.unpack [22200768,22128068,22195652], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [72529348,5350856], by decide +kernel⟩,⟨Compact54Packed.unpack [5351880,72527304], by decide +kernel⟩,⟨Compact54Packed.unpack [22200776,4400910797,21862861,22060493,5349837], by decide +kernel⟩,⟨Compact54Packed.unpack [22128076,55750092], by decide +kernel⟩,⟨Compact54Packed.unpack [38976972,38904272], by decide +kernel⟩,⟨Compact54Packed.unpack [89304528], by decide +kernel⟩]
private def p5 : List P := [⟨Compact54Packed.unpack [5424592,21993941,22126037,38904276], by decide +kernel⟩,⟨Compact54Packed.unpack [89304532], by decide +kernel⟩,⟨Compact54Packed.unpack [5424596,38904280,22195672], by decide +kernel⟩,⟨Compact54Packed.unpack [72529368,38836701], by decide +kernel⟩,⟨Compact54Packed.unpack [5348829,38904284,22195676], by decide +kernel⟩,⟨Compact54Packed.unpack [72529372,5348832], by decide +kernel⟩]
private def p6 : List P := [⟨Compact54Packed.unpack [38904288,38972896], by decide +kernel⟩,⟨Compact54Packed.unpack [55753184,22126052], by decide +kernel⟩,⟨Compact54Packed.unpack [5350884,72526308], by decide +kernel⟩,⟨Compact54Packed.unpack [38976996,21860841,21992937,5347817], by decide +kernel⟩,⟨Compact54Packed.unpack [38903272,38971880], by decide +kernel⟩,⟨Compact54Packed.unpack [72529384,5347820], by decide +kernel⟩]
private def p7 : List P := [⟨Compact54Packed.unpack [38903276,38971884], by decide +kernel⟩,⟨Compact54Packed.unpack [72529388,21926385], by decide +kernel⟩,⟨Compact54Packed.unpack [22124017,55679472,5417456], by decide +kernel⟩,⟨Compact54Packed.unpack [89304560], by decide +kernel⟩,⟨Compact54Packed.unpack [5424624,55679476,5417460], by decide +kernel⟩,⟨Compact54Packed.unpack [89304564], by decide +kernel⟩]
private def p8 : List P := [⟨Compact54Packed.unpack [5424628,38834681,5346809,38902264], by decide +kernel⟩,⟨Compact54Packed.unpack [5350904,72526328], by decide +kernel⟩,⟨Compact54Packed.unpack [38977016,38901244], by decide +kernel⟩,⟨Compact54Packed.unpack [22127100,55749116], by decide +kernel⟩,⟨Compact54Packed.unpack [55753212,22124032], by decide +kernel⟩,⟨Compact54Packed.unpack [38903296,38971904], by decide +kernel⟩]
private def p9 : List P := [⟨Compact54Packed.unpack [72529408], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++ p8 ++ p9
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 128 36 8 = true := by decide +kernel
private theorem i44 : checks ts 128 44 6 = true := by decide +kernel
private theorem rows : checks ts 128 36 14 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 14 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6thinwide
