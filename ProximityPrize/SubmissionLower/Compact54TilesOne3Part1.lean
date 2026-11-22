import ProximityPrize.SubmissionLower.Compact54RetainedTiltedBatch
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top12
private abbrev P := PaidBatch .one3 12
private def p0 : List P := [⟨unpack [69729620017,26511511845,26310323493,9180793125,8979525033,8828533161,4533634473,4399418805], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [70897105,20566481,21663027673,8811751897,3789272,3789276,3789280,4416190949], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [121225701,70895077,37341669,20565476,20565480,20565484,37341680,37341684], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [54117880,54117884,54117888,37337605,37338629,70894084,17200288265,20489737], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [20559369,70894088,70894092], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 131 36 8 = true := by decide +kernel
private theorem i44 : checks ts 131 44 8 = true := by decide +kernel
private theorem i52 : checks ts 131 52 1 = true := by decide +kernel
private theorem rows : checks ts 131 36 17 = true := (checks_join i36 (checks_join i44 (i52)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 13 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one3 13
private def p0 : List P := [⟨unpack [56945384501,22149569857,21897917761,4801940801,8878863785,4533567913,4483303849,104452541], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [87673305,37342681,3789272,3789276,3789280,17317797349,4466455013,138002917], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [70895077,20565476,20565480,20565484,4382636529,37341680,37341684,54117880], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [54117884,54117888,54117892,12905389577,20557321,20560393,20561417,70894088], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [70894092], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 131 39 8 = true := by decide +kernel
private theorem i47 : checks ts 131 47 6 = true := by decide +kernel
private theorem rows : checks ts 131 39 14 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 14 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne3
