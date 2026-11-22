import ProximityPrize.SubmissionLower.Compact54RetainedTiltedBatch
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wider
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .two6wider 1
private def p0 : List P := [⟨unpack [23442557959,23241237519,90854603799,52688294967,26917026999,30809348279,26699987127,21818283339], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [17456213323,4638490955,30491892075,8715349391,4403607951,17472977303,8883047831,8765610399], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [4453868959,41533855,24757663,7980452,41531819,24755627,24756648,108637615], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [91861423,58308015,24756652,41532848,34518148535,58309044,58309048,75085244], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [75085248,91858375,41527751,91861444,30139369931,4369979851,75080139,108637640], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [108637644,12926347731,125413840,125413844,125413848], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 118 3 8 = true := by decide +kernel
private theorem i11 : checks ts 118 11 8 = true := by decide +kernel
private theorem i19 : checks ts 118 19 8 = true := by decide +kernel
private theorem i27 : checks ts 118 27 8 = true := by decide +kernel
private theorem i35 : checks ts 118 35 8 = true := by decide +kernel
private theorem i43 : checks ts 118 43 7 = true := by decide +kernel
private theorem rows : checks ts 118 3 47 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 3 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6wider 2
private def p0 : List P := [⟨unpack [27452315659,44130055191,82264678435,22740971583,30675132611,43510759619,9520590019,35071800627], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [30726773043,21902033227,17540094283,13446248791,8732129647,192529775,125417875,91864467], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58311059,26027825567,7980444,4520974755,4437090723,4403603875,108638627,75085219], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [24756640,24756644,41532840,41532844,13027019187,58309040,75085236,75085240], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58304959,24751551,91861436,91861440,91857351,75081159,108637636,108637640], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [125413836,25811114451,41448915,125413840,8614611415,4319647191,125413844,7970267], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [142190040], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 118 6 8 = true := by decide +kernel
private theorem i14 : checks ts 118 14 8 = true := by decide +kernel
private theorem i22 : checks ts 118 22 8 = true := by decide +kernel
private theorem i30 : checks ts 118 30 8 = true := by decide +kernel
private theorem i38 : checks ts 118 38 8 = true := by decide +kernel
private theorem i46 : checks ts 118 46 4 = true := by decide +kernel
private theorem rows : checks ts 118 6 44 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 4 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6wider 3
private def p0 : List P := [⟨unpack [23308346383,39902198807,82197570599,18446005311,26480829623,43527536823,9554144439,35004759363], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [26415030595,17724506435,17590424899,4772636995,13395983715,4487493999,4437164399,41533843], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7980435,7980436,7980440,108638623,75085215,58309023,24755615,24756636], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [24756640,8748832167,4420313511,41532836,41532840,58309036,75085232,91859383], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58305975,75085236,91861432,91861436,91861440,21566137797,8681721287,91857351], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [58303943,108637636,108637640,4336425423,125413836,125413840,142190036,7903707], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [7970267,142190040], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 118 9 8 = true := by decide +kernel
private theorem i17 : checks ts 118 17 8 = true := by decide +kernel
private theorem i25 : checks ts 118 25 8 = true := by decide +kernel
private theorem i33 : checks ts 118 33 8 = true := by decide +kernel
private theorem i41 : checks ts 118 41 8 = true := by decide +kernel
private theorem i49 : checks ts 118 49 1 = true := by decide +kernel
private theorem rows : checks ts 118 9 41 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 5 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two6wider 4
private def p0 : List P := [⟨unpack [31765245971,52418007071,60756296751,5628215363,34954380487,22187387079,18159325427,22034867443], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [13781531891,17573645655,8966938967,8748838259,4453939571,21885183355,91865475,75089283], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [7980436,4386827675,91862427,58309019,24755611,24756632,24756636,41532832], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [41532836,30273515947,58309032,58309036,158900659,142190003,108636595,58305971], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [24752563,75085232,8748830135,4437088695,75085236,91861432,91861436,108637632], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩,⟨unpack [108637636,12959907275,108637640,125413836,125413840,142190036,7903707,7970267], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def p1 : List P := [⟨unpack [7971291,142190040], Compact54RetainedTiltedBatch.paid (by decide +kernel)⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 118 12 8 = true := by decide +kernel
private theorem i20 : checks ts 118 20 8 = true := by decide +kernel
private theorem i28 : checks ts 118 28 8 = true := by decide +kernel
private theorem i36 : checks ts 118 36 8 = true := by decide +kernel
private theorem i44 : checks ts 118 44 6 = true := by decide +kernel
private theorem rows : checks ts 118 12 38 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤118) (hj : a.j≤49) :
    Covered 6 .two6wider a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

end Compact50PriceTableTwo6wider
