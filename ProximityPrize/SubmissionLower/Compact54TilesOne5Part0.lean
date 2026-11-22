import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .one5 1
private def p0 : List P := [⟨unpack [5721164807,4899083275,18808380429,44294090769,116823055393,27298698397,35352894705,48070689009], by decide +kernel⟩,⟨unpack [26679750897,39412969813,43708799317,5019274589,34699642297,26109847995,4551198157], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem rows : checks ts 130 3 48 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 2 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one5 2
private def p0 : List P := [⟨unpack [18909042699,35972590609,108199563293,18828015681,35470332133,43909936357,22535774437,43440024981], by decide +kernel⟩,⟨unpack [17586330025,38910719437,26025958861,17419319757,25874618865,12889471497,4573705], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 5 = true := by decide +kernel
private theorem rows : checks ts 130 6 45 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 3 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one5 3
private def p0 : List P := [⟨unpack [31962833933,57247155225,82715638829,30941347129,30807399737,13677870393,35000567149,17838336365], by decide +kernel⟩,⟨unpack [43171587541,21596773869,13006910957,4366648825,21478855177], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 2 = true := by decide +kernel
private theorem rows : checks ts 130 9 42 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 4 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one5 4
private def p0 : List P := [⟨unpack [35922259985,65602212893,57096836149,43809461561,30874239289,30555742565,9198354789,34899898761], by decide +kernel⟩,⟨unpack [21647106525,8779053533,4366648825,30119461373,38658856457,4357641,17184367113,4568585], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 7 = true := by decide +kernel
private theorem rows : checks ts 130 12 39 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 5 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one5 5
private def p0 : List P := [⟨unpack [44764904469,82682079269,18693797953,39514499369,35102363945,13744977193,4685415853,43222121929], by decide +kernel⟩,⟨unpack [25942004189,13074017757,34431003129,25841274361,4366646777,4565513], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 4 = true := by decide +kernel
private theorem rows : checks ts 130 15 36 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 6 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one5 6
private def p0 : List P := [⟨unpack [48824993817,78370338857,5892785221,30991677737,30807398697,9466788137,43440228757,34850633109], by decide +kernel⟩,⟨unpack [4551198149,21663881693,13074018781,4349870589,21350917], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 1 = true := by decide +kernel
private theorem rows : checks ts 130 18 33 = true := (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 7 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one5 7
private def p0 : List P := [⟨unpack [52918637597,69780408369,30790355249,26411772209,5087937841,43608135017,26445054313,13141060045], by decide +kernel⟩,⟨unpack [8829385165,8762203617,4349871601,38127105,38128129,38658856457,4357641,4299536905], by decide +kernel⟩,⟨unpack [4571657], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 6 = true := by decide +kernel
private theorem rows : checks ts 130 21 30 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 8 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one5 8
private def p0 : List P := [⟨unpack [57331703841,52717983797,26411768145,21949035857,39195730313,22015871369,13107574213,4517643717], by decide +kernel⟩,⟨unpack [17301807597,8644834813,4333093373,38128125,4571657,4572681,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 3 = true := by decide +kernel
private theorem rows : checks ts 130 24 27 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 9 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one5 9
private def p0 : List P := [⟨unpack [61458902053,35672336441,35051760997,26411766117,17654066549,9030582645,4433756641,155568609], by decide +kernel⟩,⟨unpack [13023686121,4433755625,21512819201,38119937,21349893,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem rows : checks ts 130 27 24 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 10 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one5 10
private def p0 : List P := [⟨unpack [65602877481,18609911873,30891014469,22284572997,13610758469,8946827673,4366647793,71682545], by decide +kernel⟩,⟨unpack [8678388213,4383423989,21349893,4573700,21479332361,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 5 = true := by decide +kernel
private theorem rows : checks ts 130 30 21 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 11 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one5 11
private def p0 : List P := [⟨unpack [65535771693,5825676357,26629604665,26428547385,9332571449,323340725,17385693657,8795829721], by decide +kernel⟩,⟨unpack [4383425005,21348869,21349893,4573700,25774163465,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 2 = true := by decide +kernel
private theorem rows : checks ts 130 33 18 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 12 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one5 12
private def p0 : List P := [⟨unpack [61224030257,26629869881,22116805945,5037606201,13107572181,4517641685,122013165,88459757], by decide +kernel⟩,⟨unpack [4573700,21479264777,4565513,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 7 = true := by decide +kernel
private theorem rows : checks ts 130 36 15 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 13 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one5 13
private def p0 : List P := [⟨unpack [48439794741,26378214741,17670846805,8829385165,4484089293,21596773865,8728720873,54904317], by decide +kernel⟩,⟨unpack [38128125,17184366089,4567561,4571657,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 4 = true := by decide +kernel
private theorem rows : checks ts 130 39 12 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 14 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne5
