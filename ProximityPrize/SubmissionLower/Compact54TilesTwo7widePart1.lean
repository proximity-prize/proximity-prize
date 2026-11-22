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

namespace Top4
private abbrev P := PaidBatch .two7wide 4
private def p0 : List P := [⟨unpack [32017166355,48274296863,65034747951,1332920387,35055108291,26381362371,26665963799,17992281367], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [13127427415,8765355351,13412565355,13211242859,4638089579,141866371,108312963,74759555], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41206147,7651724,4403276179,108310931,7651728,24427924,24427928,41204124], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41204128,57980324,57980328,91531695,41201071,74756524,74756528,74756532], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4503867835,4403206587,91532728,125084095,74753471,91532732,91532736,108308932], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [108308936,108308940,125085136,91462103,74751447,125085140,17304808923,125085144], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [141861340,141861344,34433806823,141861348,8647836139,4352871915,158637544,21515884015], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41129455,24418799,158637548,158637552,175413748], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 125 12 8 = true := by decide +kernel
private theorem i20 : checks ts 125 20 8 = true := by decide +kernel
private theorem i28 : checks ts 125 28 8 = true := by decide +kernel
private theorem i36 : checks ts 125 36 8 = true := by decide +kernel
private theorem i44 : checks ts 125 44 5 = true := by decide +kernel
private theorem rows : checks ts 125 12 37 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 6 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two7wide 5
private def p0 : List P := [⟨unpack [35959815191,43945779235,56714497075,22052834567,17623655687,9000171783,22303891731,17908529427], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4386503019,91537771,4571047283,4470386035,175420787,74758531,41205123,7651712], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [7651716,7651720,24427916,8899497363,4554201491,292856211,24427920,34769616279], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41204116,41204120,91532703,41202079,57980316,57980320,57980324,74756520], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [74756524,74756528,91530679,41200055,91532724,91532728,91532732,13110573507], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4520643011,108308928,108308932,108308936,125085132,108239315,74751443,125085136], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [125085140,21599773147,141861336,4352872927,141861340,141861344,158637540,158637544], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [41128431,41129455,24418799,158637548,158637552,175413748], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 125 15 8 = true := by decide +kernel
private theorem i23 : checks ts 125 23 8 = true := by decide +kernel
private theorem i31 : checks ts 125 31 8 = true := by decide +kernel
private theorem i39 : checks ts 125 39 8 = true := by decide +kernel
private theorem i47 : checks ts 125 47 2 = true := by decide +kernel
private theorem rows : checks ts 125 15 34 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤125) (hj : a.j≤48) :
    Covered 7 .two7wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

end Compact50PriceTableTwo7wide
