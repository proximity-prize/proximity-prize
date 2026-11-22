import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .one4 1
private def p0 : List P := [⟨unpack [2164329477,973148169,4597027849,18791537677,44377976849,121084206113,6124213333,35503889641], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [48036741353,30924124393,14043582709,39328887145,30739159401,13391307153,34749579689,21881529769], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [17452416441,34414033405,12939410941,54513149,4299070985], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 1 = true := by decide +kernel
private theorem rows : checks ts 130 3 49 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51)))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 2 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one4 2
private def p0 : List P := [⟨unpack [15033440265,32013166609,69896914969,69931011121,39463307573,35235983669,26411177301,30572196181], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [13123891665,8812151249,239062481,43104086501,21579535857,104771057,43020670457,17183834633], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8594113033], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 6 = true := by decide +kernel
private theorem rows : checks ts 130 6 46 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 3 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one4 3
private def p0 : List P := [⟨unpack [32063497229,56826676249,86926326829,39664633097,31108525321,35051441445,30723191077,13157446085], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8795374021,289394117,25991876045,13140666829,43070531053,4366254585,71289337,43003892221], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [30085512709,8610815493,4299143689], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 3 = true := by decide +kernel
private theorem rows : checks ts 130 9 43 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 4 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one4 4
private def p0 : List P := [⟨unpack [36022923281,61340537885,65602621489,30906930497,30907462977,26360845645,26277228877,725536077], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [34799366561,13090337225,8745042377,21646644701,8778591709,4383031793,104843761,4349409789], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20958717,4181508,17183905289,4106761,4178441,4179465,4181512], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem rows : checks ts 130 12 40 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 5 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one4 5
private def p0 : List P := [⟨unpack [40049458197,69712372773,39967041593,26779739413,30806540565,17972109589,39345864037,17603409269], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4768844149,26042204617,17452408265,8812147157,4450074077,188728797,104843753,71290345], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4181500,4181504,4315921925,20957700,25773696521,20957704], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 5 = true := by decide +kernel
private theorem rows : checks ts 130 15 37 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 6 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one4 6
private def p0 : List P := [⟨unpack [48774400025,91070298153,30974310653,34984204541,17821121789,34899904905,30605471113,17636825493], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [13258042773,13140671897,339660185,21680131545,4433296857,4399810009,20958701,8694705649], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4382964209,71288309,20957685,4181492,4181496,54510077,20957692,20957696], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4315850245,20957700,4299143689,37733896], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 2 = true := by decide +kernel
private theorem rows : checks ts 130 18 34 = true := (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 7 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one4 7
private def p0 : List P := [⟨unpack [57079125021,69712907313,26562170145,30622460193,5070833953,30873376073,26578941257,13207710121], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8862480809,322880937,104843741,71290333,21629866465,4382964205,121618925,4181488], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4181492,8661150201,4366185977,20956665,20957688,20957692,37733888,20954629], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37733892,17183904265,4105737,37733896], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 7 = true := by decide +kernel
private theorem rows : checks ts 130 21 31 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 8 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one4 8
private def p0 : List P := [⟨unpack [61223100449,52684168245,30923710761,26662830377,22133185865,21931930953,641649993,8828925369], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4500406713,239061433,20958693,17301413353,4433293801,104841709,71288301,4181484], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4181488,87996917,88063477,20957684,34430738937,20957688,20957692,21512357377], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37733888,37733892,12889005577,4107785,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 4 = true := by decide +kernel
private theorem rows : checks ts 130 24 28 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 9 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one4 9
private def p0 : List P := [⟨unpack [65602481189,35604966461,35152096577,26377621825,17620118889,13241336169,4450075073,4399811009], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [21680198101,8812145109,4517180885,222215637,71289309,37735901,121618921,71288297], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4181480,4181484,20957680,20957684,20957688,37733884,30102220289,17217392129], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37733888,37733892,4299072009,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 1 = true := by decide +kernel
private theorem rows : checks ts 130 27 25 = true := (checks_join i27 (checks_join i35 (checks_join i43 (i51))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 10 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one4 10
private def p0 : List P := [⟨unpack [69763233833,18542541889,30957795621,26478418213,13643986213,8862483849,4399809997,104844749], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [17418787281,8812146129,4433295837,171950557,71288297,20957673,4181480,4181484], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20957680,20957684,20957688,30119066109,37733884,4315920897,37733888,37733892], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4299075081,4299077129,4177417,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 6 = true := by decide +kernel
private theorem rows : checks ts 130 30 22 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 11 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one4 11
private def p0 : List P := [⟨unpack [69696128045,5758306373,26696385817,30655947033,5087478041,4483631525,13291594153,8946364841], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4601068969,104843733,54513109,138397145,4181476,4181480,4181484,20957680], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [88063477,71287285,20957684,21545911801,71212537,20957688,37733884,4332630529], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37730817,37733888,37733892,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 3 = true := by decide +kernel
private theorem rows : checks ts 130 33 19 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 12 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one4 12
private def p0 : List P := [⟨unpack [65434849329,26511839525,26327493925,5020502309,8946298285,8828926381,289326509,104843733], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [54513109,21680198105,8795367897,4181476,4382964201,121618921,4181480,4181484], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20957680,20956661,20957684,20957688,37733884,4315920897,37733888,4315854341], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37733892,4177417,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem rows : checks ts 130 36 16 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 13 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one4 13
private def p0 : List P := [⟨unpack [52650613813,22166740289,21948708161,641649985,8845702581,4500406709,239061429,20958685], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4181476,17318190569,4433293801,121618921,71288297,4181480,4181484,20957680], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [87996917,88063477,20957684,20957688,37733884,37733888,37733892,54510088], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 5 = true := by decide +kernel
private theorem rows : checks ts 130 39 13 = true := (checks_join i39 (i47))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 14 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne4
