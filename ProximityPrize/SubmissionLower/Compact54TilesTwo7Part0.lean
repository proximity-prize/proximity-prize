import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)
open Compact54Packed (unpack)

namespace Top1
private abbrev P := PaidBatch .two7 1
private def p0 : List P := [⟨unpack [23624944647,40773428239,125415214111,44079271151,52434794735,22571363567,43224365511,30339605959], by decide +kernel⟩,⟨unpack [42989342207], by decide +kernel⟩]
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
    Covered 3 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two7 2
private def p0 : List P := [⟨unpack [40723093515,53289959451,82801554475,35154261323,30792456523,9384737099,47552610751,308244925], by decide +kernel⟩,⟨unpack [38710286843,25826531835,56735227], by decide +kernel⟩]
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
    Covered 4 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two7 3
private def p0 : List P := [⟨unpack [40723096591,53155744799,69933432879,35087417683,26363274579,761250131,47670185379,34785426851], by decide +kernel⟩,⟨unpack [21615453667,157400547,38694102525,21498012163,6404615], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 129 9 8 = true := by decide +kernel
private theorem i17 : checks ts 129 17 8 = true := by decide +kernel
private theorem i25 : checks ts 129 25 8 = true := by decide +kernel
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 9 40 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 5 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two7 4
private def p0 : List P := [⟨unpack [40622436371,61426915363,48576042039,39381981531,30792450395,17773338999,13428176247,38778122729], by decide +kernel⟩,⟨unpack [8646669819,56738299,17186267655], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 129 12 8 = true := by decide +kernel
private theorem i20 : checks ts 129 20 8 = true := by decide +kernel
private theorem i28 : checks ts 129 28 8 = true := by decide +kernel
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 12 37 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 6 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two7 5
private def p0 : List P := [⟨unpack [45002013719,57165703207,35758252091,35036817767,26396822887,17622477195,4804689291,12958411255], by decide +kernel⟩,⟨unpack [4368480759,21514718719,39953919,42972429827,6406663], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 129 15 8 = true := by decide +kernel
private theorem i23 : checks ts 129 23 8 = true := by decide +kernel
private theorem i31 : checks ts 129 31 8 = true := by decide +kernel
private theorem i39 : checks ts 129 39 8 = true := by decide +kernel
private theorem i47 : checks ts 129 47 2 = true := by decide +kernel
private theorem rows : checks ts 129 15 34 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 7 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two7 6
private def p0 : List P := [⟨unpack [48994994203,65571354667,10173003843,35137747263,22168968511,5106545983,47552743871,4553031103], by decide +kernel⟩,⟨unpack [17320484327,4435587559,30121359867,56728057,39960063,39961087,23181827], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 129 18 8 = true := by decide +kernel
private theorem i26 : checks ts 129 26 8 = true := by decide +kernel
private theorem i34 : checks ts 129 34 8 = true := by decide +kernel
private theorem i42 : checks ts 129 42 7 = true := by decide +kernel
private theorem rows : checks ts 129 18 31 = true := (checks_join i18 (checks_join i26 (checks_join i34 (i42))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 8 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two7 7
private def p0 : List P := [⟨unpack [44716807199,57031753775,10156226627,30792450383,17840447823,5022659919,4536253883,43224225223], by decide +kernel⟩,⟨unpack [12991963631,4402033135,73514487,39961079,25809682943,39951869,39959039,6406656], by decide +kernel⟩,⟨unpack [6406660], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 129 21 8 = true := by decide +kernel
private theorem i29 : checks ts 129 29 8 = true := by decide +kernel
private theorem i37 : checks ts 129 37 8 = true := by decide +kernel
private theorem i45 : checks ts 129 45 4 = true := by decide +kernel
private theorem rows : checks ts 129 21 28 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 9 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .two7 8
private def p0 : List P := [⟨unpack [52920868899,48408269879,22168966479,17672678735,643809615,35003130223,26413598063,8864771527], by decide +kernel⟩,⟨unpack [4519475655,73515499,8663441911,39959039,39960063,6406652,6406656,6406660], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 129 24 8 = true := by decide +kernel
private theorem i32 : checks ts 129 32 8 = true := by decide +kernel
private theorem i40 : checks ts 129 40 8 = true := by decide +kernel
private theorem i48 : checks ts 129 48 1 = true := by decide +kernel
private theorem rows : checks ts 129 24 25 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 10 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two7 9
private def p0 : List P := [⟨unpack [52887514151,35624034363,39281716587,22051525995,13394554219,4838243691,8730553831,140622311], by decide +kernel⟩,⟨unpack [107068911,39961071,21548340727,6406648,6406652,34382769667,23106049,6406656], by decide +kernel⟩,⟨unpack [6406660], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 129 27 8 = true := by decide +kernel
private theorem i35 : checks ts 129 35 8 = true := by decide +kernel
private theorem i43 : checks ts 129 43 6 = true := by decide +kernel
private theorem rows : checks ts 129 27 22 = true := (checks_join i27 (checks_join i35 (i43)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 11 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two7 10
private def p0 : List P := [⟨unpack [52871002155,22856576063,34969975147,17773337963,9049321867,4704025995,90291695,39961071], by decide +kernel⟩,⟨unpack [17236598267,4351701499,56736251,6406648,30104582655,39950845,6406652,6406656], by decide +kernel⟩,⟨unpack [23182852], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 129 30 8 = true := by decide +kernel
private theorem i38 : checks ts 129 38 8 = true := by decide +kernel
private theorem i46 : checks ts 129 46 3 = true := by decide +kernel
private theorem rows : checks ts 129 30 19 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 12 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two7 11
private def p0 : List P := [⟨unpack [52753564719,10105894979,30742119763,17756562771,4603361711,308396463,13059073503,4469143007], by decide +kernel⟩,⟨unpack [25843238391,73507317,56737275,6406648,6406652,6406656,6406660], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 129 33 8 = true := by decide +kernel
private theorem i41 : checks ts 129 41 8 = true := by decide +kernel
private theorem rows : checks ts 129 33 16 = true := (checks_join i33 (i41))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 13 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two7 12
private def p0 : List P := [⟨unpack [52636127283,26514264379,17739787579,710918459,8881548739,4536252867,73515495,21581828591], by decide +kernel⟩,⟨unpack [107063791,6406648,39959039,39960063,6406652,6406656,6406660], by decide +kernel⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 129 36 8 = true := by decide +kernel
private theorem i44 : checks ts 129 44 5 = true := by decide +kernel
private theorem rows : checks ts 129 36 13 = true := (checks_join i36 (i44))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤129) (hj : a.j≤48) :
    Covered 14 .two7 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo7
