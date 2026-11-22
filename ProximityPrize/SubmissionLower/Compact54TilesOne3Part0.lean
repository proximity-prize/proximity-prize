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

namespace Top1
private abbrev P := PaidBatch .one3 1
private def p0 : List P := [⟨unpack [2181106693,1090588681,4630582281,13975952397,39326657553,133952197661,889328733,14697830493], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [27147447477,39999785141,39546810593,60837697761,5353181457,39697721621,22015220109,21914694029], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [9063352717,34715562425,355964345,30152151545,17267536377,8677606905,54120961], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 131 3 8 = true := by decide +kernel
private theorem i11 : checks ts 131 11 8 = true := by decide +kernel
private theorem i19 : checks ts 131 19 8 = true := by decide +kernel
private theorem i27 : checks ts 131 27 8 = true := by decide +kernel
private theorem i35 : checks ts 131 35 8 = true := by decide +kernel
private theorem i43 : checks ts 131 43 8 = true := by decide +kernel
private theorem i51 : checks ts 131 51 2 = true := by decide +kernel
private theorem rows : checks ts 131 3 50 = true := (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51)))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 2 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one3 2
private def p0 : List P := [⟨unpack [10201077771,22582993933,44159482901,112510920741,35268618481,47868579057,22367550705,39680943385], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [30956866873,26276629897,17703610761,9129630093,13123567049,4567190985,34631675341,25807000069], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8627273221,4332308997,12905459209,3789325], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 131 6 8 = true := by decide +kernel
private theorem i14 : checks ts 131 14 8 = true := by decide +kernel
private theorem i22 : checks ts 131 22 8 = true := by decide +kernel
private theorem i30 : checks ts 131 30 8 = true := by decide +kernel
private theorem i38 : checks ts 131 38 8 = true := by decide +kernel
private theorem i46 : checks ts 131 46 7 = true := by decide +kernel
private theorem rows : checks ts 131 6 47 = true := (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 3 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one3 3
private def p0 : List P := [⟨unpack [26710189069,52514537497,95364609065,1714802761,26962896113,35084072189,43624274173,9516205309], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [18272305413,31174972677,21897910689,17519128993,34732406189,4483302877,4416196061,12989346293], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4399415797,70897149,37343741,30085117449,21495256585,20557321,3789320,17183293965], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [3787277,3789324], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 131 9 8 = true := by decide +kernel
private theorem i17 : checks ts 131 17 8 = true := by decide +kernel
private theorem i25 : checks ts 131 25 8 = true := by decide +kernel
private theorem i33 : checks ts 131 33 8 = true := by decide +kernel
private theorem i41 : checks ts 131 41 8 = true := by decide +kernel
private theorem i49 : checks ts 131 49 4 = true := by decide +kernel
private theorem rows : checks ts 131 9 44 = true := (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 4 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one3 4
private def p0 : List P := [⟨unpack [31744339985,61424291869,74041035825,30806478121,30655622441,5053599017,30839427413,26511176021], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [30504137125,13207383481,8845311417,4550412729,21679803869,13089940957,104452577,4382637561], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [87672313,70896121,37342713,3789308,3789312,20565508,25790083593,4315526665], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20565512,37341708], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 131 12 8 = true := by decide +kernel
private theorem i20 : checks ts 131 20 8 = true := by decide +kernel
private theorem i28 : checks ts 131 28 8 = true := by decide +kernel
private theorem i36 : checks ts 131 36 8 = true := by decide +kernel
private theorem i44 : checks ts 131 44 8 = true := by decide +kernel
private theorem i52 : checks ts 131 52 1 = true := by decide +kernel
private theorem rows : checks ts 131 12 41 = true := (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 5 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one3 5
private def p0 : List P := [⟨unpack [39914847253,69779350565,44278589497,31007466789,35067888933,35201432901,30906802501,21864360313], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [17451958649,8795046333,4466527677,26025100753,13140271569,8794976729,4500078041,70897129], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37343721,104449521,70896113,3789300,3789304,20565500,20565504,37341700], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20414985,37341704,8593715725,3784205,3785229,54117900], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 131 15 8 = true := by decide +kernel
private theorem i23 : checks ts 131 23 8 = true := by decide +kernel
private theorem i31 : checks ts 131 31 8 = true := by decide +kernel
private theorem i39 : checks ts 131 39 8 = true := by decide +kernel
private theorem i47 : checks ts 131 47 6 = true := by decide +kernel
private theorem rows : checks ts 131 15 38 = true := (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 6 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one3 6
private def p0 : List P := [⟨unpack [48874932249,91053127721,1597362249,30957140217,39295752441,13660176633,17670052245,13291269525], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8929197461,39110855073,30521258401,4500081077,138006985,17435169233,4399414761,104449513], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70896105,37342697,3789292,3789296,20565492,8677535225,4382636537,20565496], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37341692,37341696,37339653,54117892,54117896,4298679821,54117900], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 131 18 8 = true := by decide +kernel
private theorem i26 : checks ts 131 26 8 = true := by decide +kernel
private theorem i34 : checks ts 131 34 8 = true := by decide +kernel
private theorem i42 : checks ts 131 42 8 = true := by decide +kernel
private theorem i50 : checks ts 131 50 3 = true := by decide +kernel
private theorem rows : checks ts 131 18 35 = true := (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 7 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one3 7
private def p0 : List P := [⟨unpack [57162880029,73940372529,30655155473,30622002449,5019979025,30789096797,30772917597,13257715097], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8895643033,4600744345,17636496801,9046632865,138006977,4399414757,104449509,70896101], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20565477,3789284,3789288,20565484,20565488,4399412725,20565492,37341688], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37341692,54115841,37339649,54117888,54117892,30085117449,54117896,30068266509], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70894092], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 131 21 8 = true := by decide +kernel
private theorem i29 : checks ts 131 29 8 = true := by decide +kernel
private theorem i37 : checks ts 131 37 8 = true := by decide +kernel
private theorem i45 : checks ts 131 45 8 = true := by decide +kernel
private theorem rows : checks ts 131 21 32 = true := (checks_join i21 (checks_join i29 (checks_join i37 (i45))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 8 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one3 8
private def p0 : List P := [⟨unpack [57078997025,61240350773,22115883329,21965025601,9096907073,30873248077,22283649357,8862085561], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4533566905,4483302841,4399418813,54119897,20566489,17384905181,4500008413,3789280], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [3789284,70895081,37341673,20565480,20565484,20565488,104447477,70894069], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37341684,37341688,4365858301,54117884,54117888,54117892,70894088,70894092], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 131 24 8 = true := by decide +kernel
private theorem i32 : checks ts 131 32 8 = true := by decide +kernel
private theorem i40 : checks ts 131 40 8 = true := by decide +kernel
private theorem i48 : checks ts 131 48 5 = true := by decide +kernel
private theorem rows : checks ts 131 24 29 = true := (checks_join i24 (checks_join i32 (checks_join i40 (i48))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 9 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one3 9
private def p0 : List P := [⟨unpack [61222972453,44177926201,26712501549,26561841453,22149571885,13274430817,4701277537,4533632449], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [4449748417,138005957,87675333,13089940945,4516787665,3789276,3789280,3789284], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70895081,20564457,20565480,21612693997,13022831085,20565484,37341680,37341684], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [37341688,70893053,37339645,54117884,54117888,4332302853,54117892,20560393], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70894088,70894092], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 131 27 8 = true := by decide +kernel
private theorem i35 : checks ts 131 35 8 = true := by decide +kernel
private theorem i43 : checks ts 131 43 8 = true := by decide +kernel
private theorem i51 : checks ts 131 51 2 = true := by decide +kernel
private theorem rows : checks ts 131 27 26 = true := (checks_join i27 (checks_join i35 (checks_join i43 (i51))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 10 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one3 10
private def p0 : List P := [⟨unpack [61273569321,31376913469,30873581885,22132660541,13542863165,8912355705,4583837049,138005953], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [104452545,4449747401,154782153,17384905181,8761421277,4449745373,3789276,3789280], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20565476,20565480,20565484,70894065,20563441,37341680,37341684,54117880], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [54117884,25823705601,53974529,54117888,37337605,37338629,70894084,8610491913], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [70894088,70894092], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 131 30 8 = true := by decide +kernel
private theorem i38 : checks ts 131 38 8 = true := by decide +kernel
private theorem i46 : checks ts 131 46 7 = true := by decide +kernel
private theorem rows : checks ts 131 30 23 = true := (checks_join i30 (checks_join i38 (i46)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 11 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one3 11
private def p0 : List P := [⟨unpack [65434321965,14314488901,26679280929,26427760929,9315007777,4533635485,238670237,13207380417], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [8828531137,4449746385,154781137,87673305,37342681,3789272,3789276,3789280], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [20565476,20565480,20565484,37341680,37341684,87670265,37339641,54117880], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩,⟨unpack [25840551421,4365857277,70892029,54117884,54117888,70894084,70894088,70894092], Compact54TiltedBatch.pays_of_tilted (by decide +kernel)⟩]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 131 33 8 = true := by decide +kernel
private theorem i41 : checks ts 131 41 8 = true := by decide +kernel
private theorem i49 : checks ts 131 49 4 = true := by decide +kernel
private theorem rows : checks ts 131 33 20 = true := (checks_join i33 (checks_join i41 (i49)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 12 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

end Compact50PriceTableOne3
