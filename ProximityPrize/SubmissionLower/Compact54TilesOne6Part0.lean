/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top1
private abbrev P := PaidBatch .one6 1
private def p0 : List P := [⟨Compact54Packed.unpack [47782956037,47715269653,95431978021,47767620745,47766649993,47516814601], by decide +kernel⟩,⟨Compact54Packed.unpack [47784541449,47784881417,43490254089,21727808845,21727946061,21728005517], by decide +kernel⟩,⟨Compact54Packed.unpack [21728208269,47768812941,47769415053,43205762445,21728267725,21728470477], by decide +kernel⟩,⟨Compact54Packed.unpack [43206483405], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 3 47 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 2 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one6 2
private def p0 : List P := [⟨Compact54Packed.unpack [90733942793,91137208361,43471739021,43471750285,43472722189,43472733453], by decide +kernel⟩,⟨Compact54Packed.unpack [43473203469,43473673485,43473705357,43473716621,43474383245,43205959053], by decide +kernel⟩,⟨Compact54Packed.unpack [21730860493,17436161485], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 6 44 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 3 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one6 3
private def p0 : List P := [⟨Compact54Packed.unpack [86421677069,82547275817,43471676557,39176786061,43472528653,39177703693], by decide +kernel⟩,⟨Compact54Packed.unpack [39178238221,39178707213,43473446285,39178686861,39179417997,38910992781], by decide +kernel⟩,⟨Compact54Packed.unpack [17435894221,17436292557], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 9 41 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 4 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one6 4
private def p0 : List P := [⟨Compact54Packed.unpack [78369992721,78252440621,39177367825,34882738449,39178435857,34883806481], by decide +kernel⟩,⟨Compact54Packed.unpack [39161442705,34866878865,39162772881,34616092049,17419249105,13124483537], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 12 38 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 5 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one6 5
private def p0 : List P := [⟨Compact54Packed.unpack [74057989141,69662442541,34882338065,34882871569,34883470609,30588840209], by decide +kernel⟩,⟨Compact54Packed.unpack [34866281873,34867011985,34867807633,30321060241,13124217297,13124549073], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 15 35 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 6 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one6 6
private def p0 : List P := [⟨Compact54Packed.unpack [65467729945,65367476273,64932170005,64932841749,30571317649,30571981201], by decide +kernel⟩,⟨Compact54Packed.unpack [30572710289,30321125777,13124282833,13124614609], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem rows : checks ts 130 18 32 = true := checks_join i18 (checks_join i26 (checks_join i34 (i42)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 7 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one6 7
private def p0 : List P := [⟨Compact54Packed.unpack [120766616605,60635829401,56341205145,60637074709,56342712597,60386071953], by decide +kernel⟩,⟨Compact54Packed.unpack [26025562513,26026093969,30303081937,26008647121,26009309649,25892203985], by decide +kernel⟩,⟨Compact54Packed.unpack [12990197233,8695365105], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 5 = true := by decide +kernel
private theorem rows : checks ts 130 21 29 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 8 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one6 8
private def p0 : List P := [⟨Compact54Packed.unpack [107881259041,52045701277,52046304413,52046881049,52047680793,51778970005], by decide +kernel⟩,⟨Compact54Packed.unpack [26008851861,21714284949,26008117713,21713616337,26009376209,21714874833], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 2 = true := by decide +kernel
private theorem rows : checks ts 130 24 26 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 9 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one6 9
private def p0 : List P := [⟨Compact54Packed.unpack [95500528677,47751851289,43457486105,47736188309,21713886613,17419253141], by decide +kernel⟩,⟨Compact54Packed.unpack [21714410961,17419777489], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 7 = true := by decide +kernel
private theorem rows : checks ts 130 27 23 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 10 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one6 10
private def p0 : List P := [⟨Compact54Packed.unpack [82615236649,39144945949,39145677085,39145994645,38894608789,17419313617], by decide +kernel⟩,⟨Compact54Packed.unpack [17419777489], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 4 = true := by decide +kernel
private theorem rows : checks ts 130 30 20 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 11 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one6 11
private def p0 : List P := [⟨Compact54Packed.unpack [69713232941,34849981725,30555547933,34851030421,30304479637,13124282833], by decide +kernel⟩,⟨Compact54Packed.unpack [13124680145], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 1 = true := by decide +kernel
private theorem rows : checks ts 130 33 17 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 12 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one6 12
private def p0 : List P := [⟨Compact54Packed.unpack [56828071985,56326066465,26008785305,26009382297,25992466901,25875492309], by decide +kernel⟩,⟨Compact54Packed.unpack [12990197233,8695430641], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 6 = true := by decide +kernel
private theorem rows : checks ts 130 36 14 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 13 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one6 13
private def p0 : List P := [⟨Compact54Packed.unpack [43926068277,43440774433,21713886617,17419253145,21697568213,17403000277], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 3 = true := by decide +kernel
private theorem rows : checks ts 130 39 11 = true := checks_join i39 (i47)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤49) :
    Covered 14 .one6 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne6
