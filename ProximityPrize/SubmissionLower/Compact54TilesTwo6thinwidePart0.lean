import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thinwide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .two6thinwide 1
private def p0 : List P := [⟨unpack [14781844487,14732106767,31997963283,112310504479,14332835907,30941007035,52232285371,22469845179], by decide +kernel⟩,⟨unpack [22134156643,21966521699,9216040291,30556245391,8763128223,223528351,8796613035,4518491563], by decide +kernel⟩,⟨unpack [30303788491,89308619,55755211,13105958349,5424596,17352984027,4468087259,22200792], by decide +kernel⟩,⟨unpack [156346847,4367494623,22200796,13024050657,55752163,22198755,38976992,38976996], by decide +kernel⟩,⟨unpack [55753192,55753196,55750131,22196723,72529392,72529396,4317094395,89305592], by decide +kernel⟩,⟨unpack [89305596,21480107523,5349891,5350915,106081792], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 128 3 8 = true := by decide +kernel
private theorem i11 : checks ts 128 11 8 = true := by decide +kernel
private theorem i19 : checks ts 128 19 8 = true := by decide +kernel
private theorem i27 : checks ts 128 27 8 = true := by decide +kernel
private theorem i35 : checks ts 128 35 8 = true := by decide +kernel
private theorem i43 : checks ts 128 43 7 = true := by decide +kernel
private theorem rows : checks ts 128 3 47 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 3 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6thinwide 2
private def p0 : List P := [⟨unpack [14950209547,32014739475,69545379867,61208366131,22451734755,30992326883,26630521059,21933104439], by decide +kernel⟩,⟨unpack [17587877175,8729572763,4401054107,8846941607,4518422951,4484936103,17453580723,4635858355], by decide +kernel⟩,⟨unpack [55755191,22201783,89307583,55754175,5424572,21748277699,13158480323,5424576], by decide +kernel⟩,⟨unpack [22200772,22200776,21697874381,38976972,38976976,55751127,22197719,55753172], by decide +kernel⟩,⟨unpack [55753176,72460767,72527327,72529372,72529376,30186875365,4367424999,89236967], by decide +kernel⟩,⟨unpack [89305572,89305576,89305580,22194675,106081776,8645609975,106081780,12922591737], by decide +kernel⟩]
private def p1 : List P := [⟨unpack [38903291,38904315,122857976,5350908,122857980,5350912,122857984], by decide +kernel⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 128 6 8 = true := by decide +kernel
private theorem i14 : checks ts 128 14 8 = true := by decide +kernel
private theorem i22 : checks ts 128 22 8 = true := by decide +kernel
private theorem i30 : checks ts 128 30 8 = true := by decide +kernel
private theorem i38 : checks ts 128 38 8 = true := by decide +kernel
private theorem i46 : checks ts 128 46 4 = true := by decide +kernel
private theorem rows : checks ts 128 6 44 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 4 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6thinwide 3
private def p0 : List P := [⟨unpack [32081847311,48322200601,77984461865,5642240067,35052418255,39196661967,35237086495,22369036575], by decide +kernel⟩,⟨unpack [17537407315,13209021779,4635868499,13410140535,4836987255,156419463,4434537891,4384273827], by decide +kernel⟩,⟨unpack [89308583,55755175,8813386155,4484867499,5424556,5424560,22200756,72529339], by decide +kernel⟩,⟨unpack [38975931,22200760,38976956,38976960,106081735,55751111,55753156,55753160], by decide +kernel⟩,⟨unpack [72529356,72529360,89305556,72459739,22129115,89305560,89305564,4384201187], by decide +kernel⟩,⟨unpack [89235939,5351904,106081760,5417447,106081764,122857960,5350892,122857964], by decide +kernel⟩]
private def p1 : List P := [⟨unpack [34431510003,30136814067,5350896,122857968,21530307063,12940509687,5350900,122857972], by decide +kernel⟩,⟨unpack [4333867515,38902267,38903291,22127096,122857976,22127100,122857980,22127104], by decide +kernel⟩,⟨unpack [122857984], by decide +kernel⟩]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 128 9 8 = true := by decide +kernel
private theorem i17 : checks ts 128 17 8 = true := by decide +kernel
private theorem i25 : checks ts 128 25 8 = true := by decide +kernel
private theorem i33 : checks ts 128 33 8 = true := by decide +kernel
private theorem i41 : checks ts 128 41 8 = true := by decide +kernel
private theorem i49 : checks ts 128 49 1 = true := by decide +kernel
private theorem rows : checks ts 128 9 41 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤128) (hj : a.j≤49) :
    Covered 5 .two6thinwide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

end Compact50PriceTableTwo6thinwide
