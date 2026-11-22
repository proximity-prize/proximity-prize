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
open Compact54Packed (unpack)

namespace Top10
private abbrev P := PaidBatch .two7wide 10
private def p0 : List P := [⟨unpack [43761236011,31045362747,22337714415,17925574895,13261579559,8882795815,343195943,192197999], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [141867375,91536751,7651704,7651708,4537492867,4420054403,7651712,24427908], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [24427912,24427916,41204112,41204116,41204120,57980316,8865943971,4503870883], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [91532707,41202083,57980320,57980324,57980328,74756524,74756528,74756532], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [91532728,17422318015,8832388543,108307903,41200063,91532732,91532736,91532740], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [108308936,108308940,108308944,141860311,74752471,108308948,125085144,125085148], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [125085152,74750439,125085156,141861352,141861356,141861360,141861364], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 125 30 8 = true := by decide +kernel
private theorem i38 : checks ts 125 38 8 = true := by decide +kernel
private theorem i46 : checks ts 125 46 3 = true := by decide +kernel
private theorem rows : checks ts 125 30 19 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 12 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two7wide 11
private def p0 : List P := [⟨unpack [35221636143,26800728123,22237316351,13546790143,8949902643,8798910771,192199015,125091175], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [74760551,7651704,7651708,7651712,24427908,4403277195,91534731,24427912], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [24427916,24427920,41204116,41204120,4537425311,4436829599,41204124,57980320], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [91532711,41202087,57980324,57980328,57980332,74756528,13160908215,4570977719], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [74756532,74756536,91532732,108307907,41200067,91532736,91532740,91532744], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [108308940,108308944,108308948,125083099,91529691,108308952,125085148,125085152], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [125085156,125085160,125085164,141861360,141861364], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 125 33 8 = true := by decide +kernel
private theorem i41 : checks ts 125 41 8 = true := by decide +kernel
private theorem rows : checks ts 125 33 16 = true := (checks_join i33 (i41))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 13 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two7wide 12
private def p0 : List P := [⟨unpack [43930259507,5510446147,17791422751,13328688415,4755600671,141868391,91537767,7651708], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [7651712,7651716,4537492875,4420054411,24427912,91534735,24426895,24427916], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [24427920,41204116,41204120,41204124,41204128,57980324,108309931,41202091], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [57980328,57980332,8849166771,4520713651,57980336,74756532,74756536,74756540], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [74756544,125085127,57977287,91532740,91532744,91532748,91532752,108308948], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [108308952,108308956,108308960,125085156,57974251,41198059,125085160,125085164], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [4319318515,24418803,125085168,141861364], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 125 36 8 = true := by decide +kernel
private theorem i44 : checks ts 125 44 5 = true := by decide +kernel
private theorem rows : checks ts 125 36 13 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 14 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo7wide
