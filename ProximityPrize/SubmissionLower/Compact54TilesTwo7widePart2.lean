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

namespace Top6
private abbrev P := PaidBatch .two7wide 6
private def p0 : List P := [⟨unpack [35825600539,48072977447,39618518071,22354357487,22203761903,17573322015,13194539295,393527583], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4453609835,158644587,108313963,30558275963,22002428283,4587756927,4503938431,208973183], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [7651708,7651712,24427908,24427912,24427916,74756499,24425875,41204112], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41204116,57980312,8966604191,4621308319,326343071,57980316,57980320,74756516], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [74756520,74756524,91530675,41200051,91532720,91532724,91532728,108308924], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [225673667,108308928,125083079,74752455,108308932,125085128,125085132,125085136], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [125085140,141861336,141861340,141861344,158637540,158637544,41128431,41129455], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [24418799,158637548,30088776179,158637552,175413748], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 125 18 8 = true := by decide +kernel
private theorem i26 : checks ts 125 26 8 = true := by decide +kernel
private theorem i34 : checks ts 125 34 8 = true := by decide +kernel
private theorem i42 : checks ts 125 42 7 = true := by decide +kernel
private theorem rows : checks ts 125 18 31 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 8 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two7wide 7
private def p0 : List P := [⟨unpack [39868912671,43710905391,26817505339,22237052135,17892087015,13160982839,8782133559,26514969923], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [17942344003,158644583,108313959,74760551,4470385019,175419771,125089147,7651704], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [7651708,24427904,24427908,24427912,41204108,4621309331,4503870867,242525587], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41204112,41204116,57980312,8966604191,4654862751,57980316,57980320,91531687], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41201063,74756516,74756520,74756524,91532720,91532724,91532728,108308924], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [108308928,141860295,74752455,108308932,108308936,125085132,125085136,125085140], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [141861336,141861340,91527651,141861344,141861348,158637544,158637548,158637552], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [25777296887,7574007,7575031,158637556], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 125 21 8 = true := by decide +kernel
private theorem i29 : checks ts 125 29 8 = true := by decide +kernel
private theorem i37 : checks ts 125 37 8 = true := by decide +kernel
private theorem i45 : checks ts 125 45 4 = true := by decide +kernel
private theorem rows : checks ts 125 21 28 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 9 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

end Compact50PriceTableTwo7wide
