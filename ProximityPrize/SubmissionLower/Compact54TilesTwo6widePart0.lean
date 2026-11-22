import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .two6wide 1
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [23373483015,32032171023,112294380571,23142510655,48526214323,61008540851,39047361927,26162601351]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [21564624333,12975847887]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 120 3 8 = true := by decide +kernel
private theorem i11 : checks ts 120 11 8 = true := by decide +kernel
private theorem i19 : checks ts 120 19 8 = true := by decide +kernel
private theorem i27 : checks ts 120 27 8 = true := by decide +kernel
private theorem i35 : checks ts 120 35 8 = true := by decide +kernel
private theorem i43 : checks ts 120 43 7 = true := by decide +kernel
private theorem rows : checks ts 120 3 47 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 3 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6wide 2
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [23256045579,40118792211,108168501283,6046531651,43996371171,48023110883,9670407395,47720968563]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [34651866527,8882137503,21665290677,34383290847]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 120 6 8 = true := by decide +kernel
private theorem i14 : checks ts 120 14 8 = true := by decide +kernel
private theorem i22 : checks ts 120 22 8 = true := by decide +kernel
private theorem i30 : checks ts 120 30 8 = true := by decide +kernel
private theorem i38 : checks ts 120 38 8 = true := by decide +kernel
private theorem i46 : checks ts 120 46 4 = true := by decide +kernel
private theorem rows : checks ts 120 6 44 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 4 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6wide 3
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [32032171023,56778572827,78440201263,48173892863,35322754303,30658894143,13562984767,25860676047]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [12975846863,42973021663,23687645,7063011]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 120 9 8 = true := by decide +kernel
private theorem i17 : checks ts 120 17 8 = true := by decide +kernel
private theorem i25 : checks ts 120 25 8 = true := by decide +kernel
private theorem i33 : checks ts 120 33 8 = true := by decide +kernel
private theorem i41 : checks ts 120 41 8 = true := by decide +kernel
private theorem i49 : checks ts 120 49 1 = true := by decide +kernel
private theorem rows : checks ts 120 9 41 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 5 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two6wide 4
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [31897956371,57115430943,65605634099,30692444495,26229713231,627754319,43560161619,9200827729]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [17337854399,4453023167,30172000713]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 120 12 8 = true := by decide +kernel
private theorem i20 : checks ts 120 20 8 = true := by decide +kernel
private theorem i28 : checks ts 120 28 8 = true := by decide +kernel
private theorem i36 : checks ts 120 36 8 = true := by decide +kernel
private theorem i44 : checks ts 120 44 6 = true := by decide +kernel
private theorem rows : checks ts 120 12 38 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 6 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6wide 5
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [35857382423,69715124259,35758974011,39516856595,30927325459,47670639999,17539180939,8966094219]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [34366516707,25776787939,12891958755]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 120 15 8 = true := by decide +kernel
private theorem i23 : checks ts 120 23 8 = true := by decide +kernel
private theorem i31 : checks ts 120 31 8 = true := by decide +kernel
private theorem i39 : checks ts 120 39 8 = true := by decide +kernel
private theorem i47 : checks ts 120 47 3 = true := by decide +kernel
private theorem rows : checks ts 120 15 35 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 7 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6wide 6
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [48793929755,74061215787,5929091139,35104651559,30658895143,5090426151,43308566927,34718840207]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [21666373047,4486575543,107726283,40540633]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 120 18 8 = true := by decide +kernel
private theorem i26 : checks ts 120 26 8 = true := by decide +kernel
private theorem i34 : checks ts 120 34 8 = true := by decide +kernel
private theorem i42 : checks ts 120 42 8 = true := by decide +kernel
private theorem rows : checks ts 120 18 32 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 8 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6wide 7
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [52887573535,65521748019,30759553339,22035409211,4956209467,43493053795,30608556387,13026109891]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [8731212227,40617435,4301955555]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 120 21 8 = true := by decide +kernel
private theorem i29 : checks ts 120 29 8 = true := by decide +kernel
private theorem i37 : checks ts 120 37 8 = true := by decide +kernel
private theorem i45 : checks ts 120 45 5 = true := by decide +kernel
private theorem rows : checks ts 120 21 29 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 9 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two6wide 8
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [52803690531,52737512503,39265198419,30658890067,21917968727,4872388951,13026109891,8731212227]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [30071753187,7063011]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 120 24 8 = true := by decide +kernel
private theorem i32 : checks ts 120 32 8 = true := by decide +kernel
private theorem i40 : checks ts 120 40 8 = true := by decide +kernel
private theorem i48 : checks ts 120 48 2 = true := by decide +kernel
private theorem rows : checks ts 120 24 26 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 10 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two6wide 9
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [61259738151,31447230523,39332441399,26464589111,13244215687,4687905159,38695038427,21498598879]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [12908735967,23838175]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 120 27 8 = true := by decide +kernel
private theorem i35 : checks ts 120 35 8 = true := by decide +kernel
private theorem i43 : checks ts 120 43 7 = true := by decide +kernel
private theorem rows : checks ts 120 27 23 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 11 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6wide 10
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [61344086059,18679772223,39248820559,17807548751,13110064551,258721191,34383428063,23764445]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [8613770719,23839199]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 120 30 8 = true := by decide +kernel
private theorem i38 : checks ts 120 38 8 = true := by decide +kernel
private theorem i46 : checks ts 120 46 4 = true := by decide +kernel
private theorem rows : checks ts 120 30 20 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 12 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6wide 11
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [69766382639,35088074027,26313599275,778683691,17388186031,4520132015,30105306587,17220412891]) (by decide +kernel),Compact54FastPrice.fastBatch (unpack [7059939]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 120 33 8 = true := by decide +kernel
private theorem i41 : checks ts 120 41 8 = true := by decide +kernel
private theorem i49 : checks ts 120 49 1 = true := by decide +kernel
private theorem rows : checks ts 120 33 17 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 13 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two6wide 12
private def p0 : List P := [Compact54FastPrice.fastBatch (unpack [52771065907,1650902087,30575006043,17656623451,12975845839,4385915343,25827119575,57388503]) (by decide +kernel)]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 120 36 8 = true := by decide +kernel
private theorem i44 : checks ts 120 44 6 = true := by decide +kernel
private theorem rows : checks ts 120 36 14 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 14 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6wide
