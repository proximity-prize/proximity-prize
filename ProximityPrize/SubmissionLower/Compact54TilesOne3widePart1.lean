import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54TilesOne3widePart0

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne3wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top13
private abbrev P := PaidBatch .one3wide 13
private def p0 : List P := [⟨Compact54Packed.unpack [56811035701,26007674145,26008140065,26008132957,25890961757,12989086077], by decide +kernel⟩,⟨Compact54Packed.unpack [8694253949,25890954649,13006125465,8644053401,4349086121,54120873], by decide +kernel⟩,⟨Compact54Packed.unpack [12988947897,8694181305,4399282617,4349018553,4315597241,20631993], by decide +kernel⟩,⟨Compact54Packed.unpack [20498881,20565441,3854785,3854788,4332372425,37407177], by decide +kernel⟩,⟨Compact54Packed.unpack [20630985,3854792,3854796,20630992,12989144533], by decide +kernel⟩,⟨Compact54Packed.unpack [8694377941,4349082069,4315595221,3852757,20630996], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [37407192,20562397,20628957,3852764], by decide +kernel⟩,⟨Compact54Packed.unpack [20631004,37407200,37272037], by decide +kernel⟩,⟨Compact54Packed.unpack [37338597,37405157,54183396], by decide +kernel⟩,⟨Compact54Packed.unpack [54183400,20628972], by decide +kernel⟩,⟨Compact54Packed.unpack [20631020,12989341169,4349013489,54048241,20494833], by decide +kernel⟩,⟨Compact54Packed.unpack [20626929,70959600], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [70959604,20560377], by decide +kernel⟩,⟨Compact54Packed.unpack [3849721,70959608], by decide +kernel⟩,⟨Compact54Packed.unpack [87735804], by decide +kernel⟩,⟨Compact54Packed.unpack [4332301825,37336577,20625921,37404160], by decide +kernel⟩,⟨Compact54Packed.unpack [37407232,37404164], by decide +kernel⟩,⟨Compact54Packed.unpack [37407236,37403144], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [54183432], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 6 = true := by decide +kernel
private theorem rows : checks ts 130 39 14 = true := checks_join i39 (i47)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 14 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne3wide
