import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact50PriceTableOne4

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top1
private abbrev P := PaidBatch .one5 1
private def p0 : List P := [⟨Compact54Packed.unpack [21609188357,21709988877,47715269653,99727010853,21592542249,47497743433], by decide +kernel⟩,⟨Compact54Packed.unpack [47498464393,47766649993,47499185353,21744323849,21744461065,47784475913], by decide +kernel⟩,⟨Compact54Packed.unpack [47784815881,47785286921,21727808845,21727946061,21728005517,21728142733], by decide +kernel⟩,⟨Compact54Packed.unpack [47768747405,47500258701,47500795277,21728202189,21728404941,21729799629], by decide +kernel⟩,⟨Compact54Packed.unpack [21730264525,21730663885,21731063245], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem rows : checks ts 130 3 48 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 2 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one5 2
private def p0 : List P := [⟨Compact54Packed.unpack [47782631433,43420436505,91137143849,47766902925,43471685773,47768017165], by decide +kernel⟩,⟨Compact54Packed.unpack [43472668941,43473138957,43473608973,47500106125,43473652109,43205293453], by decide +kernel⟩,⟨Compact54Packed.unpack [21730271629,17435507085,21728205261,21728670157,21730063821,17435364813], by decide +kernel⟩,⟨Compact54Packed.unpack [21730861517,17301617101,8711682541,4416718317], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 5 = true := by decide +kernel
private theorem rows : checks ts 130 6 45 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 3 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one5 3
private def p0 : List P := [⟨Compact54Packed.unpack [86421677069,86842308649,43471611021,39176720525,43472528653,39177703693], by decide +kernel⟩,⟨Compact54Packed.unpack [43473336589,39178708237,43473380749,39178621325,43205491085,17435305357], by decide +kernel⟩,⟨Compact54Packed.unpack [17435638157,21730195917,17435496909,17435895245,17301748173,8711748077], by decide +kernel⟩,⟨Compact54Packed.unpack [4416849389], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 2 = true := by decide +kernel
private theorem rows : checks ts 130 9 42 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 4 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one5 4
private def p0 : List P := [⟨Compact54Packed.unpack [82126516241,78252376109,39176581265,39176853649,39177367825,39177836817], by decide +kernel⟩,⟨Compact54Packed.unpack [39178371345,34883807505,39161377169,39162042769,38910525841,17435502993], by decide +kernel⟩,⟨Compact54Packed.unpack [13140737425,17418453457,17418851793,17419250129,13006781905,4400004593], by decide +kernel⟩,⟨Compact54Packed.unpack [4400137713], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 7 = true := by decide +kernel
private theorem rows : checks ts 130 12 39 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 5 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one5 5
private def p0 : List P := [⟨Compact54Packed.unpack [74057923605,73957475373,34882272529,34882806033,34883405073,34883873041], by decide +kernel⟩,⟨Compact54Packed.unpack [34866281873,34866946449,34615494033,17435568529,13140802961,17418585553], by decide +kernel⟩,⟨Compact54Packed.unpack [13123819985,17419315665,13006847441,4400070129,4400203249], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 4 = true := by decide +kernel
private theorem rows : checks ts 130 15 36 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 6 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one5 6
private def p0 : List P := [⟨Compact54Packed.unpack [69762828313,65367477297,34865694997,30571130133,30571662613,30572129557], by decide +kernel⟩,⟨Compact54Packed.unpack [34866481553,30572047761,30320528785,30186581393,13006319025,13006650801], by decide +kernel⟩,⟨Compact54Packed.unpack [13123554769,13123952081,13124283857,13006912977,4400135665,4349871601], by decide +kernel⟩,⟨Compact54Packed.unpack [37996033,38128129], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 1 = true := by decide +kernel
private theorem rows : checks ts 130 18 33 = true := checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 7 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one5 7
private def p0 : List P := [⟨Compact54Packed.unpack [60634518557,60551565361,60635763865,60636303513,60637009173,60385366293], by decide +kernel⟩,⟨Compact54Packed.unpack [30303293781,26008662357,30319465873,26024899985,30320660881,25891549585], by decide +kernel⟩,⟨Compact54Packed.unpack [13006451121,8711618993,30303016401,26008581585,13123686865,13124018641], by decide +kernel⟩,⟨Compact54Packed.unpack [13006713297,8711881169,4399870449,4400069105,4349805041,54839793], by decide +kernel⟩,⟨Compact54Packed.unpack [4333093377,38128129], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 6 = true := by decide +kernel
private theorem rows : checks ts 130 21 30 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 8 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one5 8
private def p0 : List P := [⟨Compact54Packed.unpack [112176422945,56340799645,52046239901,56341979417,51795302681,26008328537], by decide +kernel⟩,⟨Compact54Packed.unpack [21713696089,26007724437,26008321429,26008852885,21714285973,26008117713], by decide +kernel⟩,⟨Compact54Packed.unpack [26008780241,25891740113,8711681489,8711946705,12989667825,8694835697], by decide +kernel⟩,⟨Compact54Packed.unpack [8695166449,4349805041,54839793,37995009,38061569,21350913], by decide +kernel⟩,⟨Compact54Packed.unpack [4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 3 = true := by decide +kernel
private theorem rows : checks ts 130 24 27 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 9 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one5 9
private def p0 : List P := [⟨Compact54Packed.unpack [99291130917,47733894305,47734496417,47751785753,47500270873,21713296729], by decide +kernel⟩,⟨Compact54Packed.unpack [21713761625,47483874709,21713821077,21714285973,21713153489,21713749457], by decide +kernel⟩,⟨Compact54Packed.unpack [21596642769,8711681489,8711946705,8694570481,8694835697,8695166449], by decide +kernel⟩,⟨Compact54Packed.unpack [4349870577,54839793,37995009,38127105,21350913,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem rows : checks ts 130 27 24 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 10 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one5 10
private def p0 : List P := [⟨Compact54Packed.unpack [86405904425,43438995621,39144432805,43440044317,39145678109,43188910485], by decide +kernel⟩,⟨Compact54Packed.unpack [17418855829,17419254165,21713418705,17418850769,17301677521,8711813585], by decide +kernel⟩,⟨Compact54Packed.unpack [4416914897,17285096945,8644835825,4316317169,21218809,21350905], by decide +kernel⟩,⟨Compact54Packed.unpack [4332960257,37995009,38127105,4573697,4573700,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 5 = true := by decide +kernel
private theorem rows : checks ts 130 30 21 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 11 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one5 11
private def p0 : List P := [⟨Compact54Packed.unpack [74008265773,34849916189,34850580765,34598782357,17418922389,13124222357], by decide +kernel⟩,⟨Compact54Packed.unpack [17418520017,13123819985,17301744081,12939804113,4349607393,4349806049], by decide +kernel⟩,⟨Compact54Packed.unpack [8694835697,4400002545,4400201201,4316317169,21218809,21350905], by decide +kernel⟩,⟨Compact54Packed.unpack [38127105,4573697,4573700,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 2 = true := by decide +kernel
private theorem rows : checks ts 130 33 18 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 12 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one5 12
private def p0 : List P := [⟨Compact54Packed.unpack [61123104817,60368851233,30303359325,26008858973,30303883673,25891746201], by decide +kernel⟩,⟨Compact54Packed.unpack [12989739449,8694972857,13106844117,13107241429,12990001621,8695169493], by decide +kernel⟩,⟨Compact54Packed.unpack [4399870449,4400069105,4349870577,54905329,37995009,38127105], by decide +kernel⟩,⟨Compact54Packed.unpack [4573697,4573700,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 7 = true := by decide +kernel
private theorem rows : checks ts 130 36 15 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 13 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one5 13
private def p0 : List P := [⟨Compact54Packed.unpack [48221166645,47483559201,21713296733,21713827165,21713821081,21596648857], by decide +kernel⟩,⟨Compact54Packed.unpack [8694642105,8694972857,21579800021,8694904277,8695169493,8694504945], by decide +kernel⟩,⟨Compact54Packed.unpack [8694835697,8695100913,4349805041,54839793,37995009,38061569], by decide +kernel⟩,⟨Compact54Packed.unpack [21350913,4573704], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 4 = true := by decide +kernel
private theorem rows : checks ts 130 39 12 = true := checks_join i39 (i47)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤50) :
    Covered 14 .one5 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne5
