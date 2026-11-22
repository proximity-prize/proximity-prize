import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .one7 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [23455927303,57868559375,109006838819,99176111531,4687117737,55991274979,21547664885]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 129 3 8 = true := by decide +kernel
private theorem i11 : checks ts 129 11 8 = true := by decide +kernel
private theorem i19 : checks ts 129 19 8 = true := by decide +kernel
private theorem i27 : checks ts 129 27 8 = true := by decide +kernel
private theorem i35 : checks ts 129 35 8 = true := by decide +kernel
private theorem i43 : checks ts 129 43 6 = true := by decide +kernel
private theorem rows : checks ts 129 3 46 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 2 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one7 2
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [36425897995,57801456663,83488699435,86005726703,51646534125,34415778297]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 129 6 8 = true := by decide +kernel
private theorem i14 : checks ts 129 14 8 = true := by decide +kernel
private theorem i22 : checks ts 129 22 8 = true := by decide +kernel
private theorem i30 : checks ts 129 30 8 = true := by decide +kernel
private theorem i38 : checks ts 129 38 8 = true := by decide +kernel
private theorem i46 : checks ts 129 46 3 = true := by decide +kernel
private theorem rows : checks ts 129 6 43 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 3 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one7 3
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [53657478159,79277611043,32000418873,77365729787]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 129 9 8 = true := by decide +kernel
private theorem i17 : checks ts 129 17 8 = true := by decide +kernel
private theorem i25 : checks ts 129 25 8 = true := by decide +kernel
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 9 40 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 4 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one7 4
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [53640704019,83371254823,14803776573,81845249487]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 129 12 8 = true := by decide +kernel
private theorem i20 : checks ts 129 20 8 = true := by decide +kernel
private theorem i28 : checks ts 129 28 8 = true := by decide +kernel
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 12 37 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 5 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one7 5
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [53556821015,74848432171,10492033089,73171431907,51595656697]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 129 15 8 = true := by decide +kernel
private theorem i23 : checks ts 129 23 8 = true := by decide +kernel
private theorem i31 : checks ts 129 31 8 = true := by decide +kernel
private theorem i39 : checks ts 129 39 8 = true := by decide +kernel
private theorem i47 : checks ts 129 47 2 = true := by decide +kernel
private theorem rows : checks ts 129 15 34 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 6 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one7 6
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [57852184603,70503137327,68910285275,55874111997]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 129 18 8 = true := by decide +kernel
private theorem i26 : checks ts 129 26 8 = true := by decide +kernel
private theorem i34 : checks ts 129 34 8 = true := by decide +kernel
private theorem i42 : checks ts 129 42 7 = true := by decide +kernel
private theorem rows : checks ts 129 18 31 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 7 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one7 7
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [74965865503,40607128629,73104315891]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 129 21 8 = true := by decide +kernel
private theorem i29 : checks ts 129 29 8 = true := by decide +kernel
private theorem i37 : checks ts 129 37 8 = true := by decide +kernel
private theorem i45 : checks ts 129 45 4 = true := by decide +kernel
private theorem rows : checks ts 129 21 28 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 8 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one7 8
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [70704455715,32000418873,68759020029]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 129 24 8 = true := by decide +kernel
private theorem i32 : checks ts 129 32 8 = true := by decide +kernel
private theorem i40 : checks ts 129 40 8 = true := by decide +kernel
private theorem i48 : checks ts 129 48 1 = true := by decide +kernel
private theorem rows : checks ts 129 24 25 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 9 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one7 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [66409491495,23393709117,64447278593]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 129 27 8 = true := by decide +kernel
private theorem i35 : checks ts 129 35 8 = true := by decide +kernel
private theorem i43 : checks ts 129 43 6 = true := by decide +kernel
private theorem rows : checks ts 129 27 22 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 10 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one7 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [66292054059,10492033089,64547944939]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 129 30 8 = true := by decide +kernel
private theorem i38 : checks ts 129 38 8 = true := by decide +kernel
private theorem i46 : checks ts 129 46 3 = true := by decide +kernel
private theorem rows : checks ts 129 30 19 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 11 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one7 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [66410480685]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 33 16 = true := (checks_join i33 (i41))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 12 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one7 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [53508804657]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 36 13 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 13 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one7 13
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [40607128629]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 129 39 8 = true := by decide +kernel
private theorem i47 : checks ts 129 47 2 = true := by decide +kernel
private theorem rows : checks ts 129 39 10 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 14 .one7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne7
