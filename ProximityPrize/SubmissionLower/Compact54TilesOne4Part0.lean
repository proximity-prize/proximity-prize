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

namespace Top1
private abbrev P := PaidBatch .one4 1
private def p0 : List P := [p54 [13019188229,8690670605,21693212689,47698427929,13002476585,8707513385],p54 [99709972521,26021989449,21726963785,26022251657,21727225993,47766519945],p54 [26022513865,21727422665,26039618825,21744462089,47784345865,47784685833],p54 [47785091337,26023103821,21727881549,26023366029,21728143757,47499592077],p54 [47500063117,21729943949,21730212237,26023628237,21728340429,47500116429],p54 [21729669581,21730068941,21730468301,21596322253,8711289325,8711489005]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 1 = true := by decide +kernel
private theorem rows : checks ts 130 3 49 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 2 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one4 2
private def p0 : List P := [p54 [47782565897,43420370969,95432045609,47766837389,43471620237,47767820557],p54 [43472537869,47768106253,43473478925,21727943053,21728276877,43473455501],p54 [47500260749,21730141581,17435377037,21728139725,21728539085,21729867213],p54 [21730266573,21596186061,17301421517,8711087597,8711287277,8711486957],p54 [4416588269]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 6 = true := by decide +kernel
private theorem rows : checks ts 130 6 46 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 3 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one4 3
private def p0 : List P := [p54 [90716644365,86825335853,43471545485,43471753357,43472332045,43472670989],p54 [43473141005,39178512653,43473184141,43204694413,43205295501,17435175309],p54 [17435442573,43205218765,21730065869,17435366861,17301219789,8711290317],p54 [4416391629,8711219693,4416321005,8644378093,4349413869,4349345277],p54 [54380029,4315924989,20892165,20958725]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 3 = true := by decide +kernel
private theorem rows : checks ts 130 9 43 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 4 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one4 4
private def p0 : List P := [p54 [82126385169,82547277869,39176450193,39176788113,39177236753,39177705745],p54 [39178240273,39178709265,39161180561,39161780625,38910329233,17435306385],p54 [17435639185,17418256849,17418655185,17301350865,8711421393,4416522705],p54 [8694508017,4399609329,8644443633,4315924977,20892153,20958713],p54 [4332633601,37668353,37734913,4181505,4181508,4181512]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem rows : checks ts 130 12 40 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 5 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one4 5
private def p0 : List P := [p54 [77831355413,73940502577,77816020117,39177370897,34882741521,34883275025],p54 [34883742993,39161314705,34866816401,34615363985,17435438481,13140607377],p54 [17418455505,13123689937,8711220689,4416322001,4349215185,4349348305],p54 [4349346273,4349479393,8694640113,4399741425,4349477361,20892145],p54 [20958705,20957689,4181497,4181500,37667329,37733889],p54 [4180481,4181504,20957700,20957704]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 5 = true := by decide +kernel
private theorem rows : checks ts 130 15 37 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 6 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one4 6
private def p0 : List P := [p54 [69762697241,69662379057,34865563925,30570933525,34866564373,30571999509],p54 [34866284945,30571851153,17434906001,13140140433,13005926801,13006193041],p54 [13006188977,13006455217,17418522065,13123822033,13006451153,4349280721],p54 [4349413841,4349411809,4315924961,20892137,20958697,4399608305],p54 [4349344241,4315922929,20957681,4181489,4181492,20824569],p54 [20956665,4180473,4181496,20957692,4332698113]]
private def p1 : List P := [p54 [37732865,20956673,20957696,20957700],p54 [37733896]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 2 = true := by decide +kernel
private theorem rows : checks ts 130 18 34 = true := checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 7 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one4 7
private def p0 : List P := [p54 [64929551389,60534723637,64930731161,60636107929,30570599701,30571066645],p54 [30319416597,26024785173,30303163733,26008532309,30571320721,30571984273],p54 [30185985425,13006058897,8711226769,13005723057,13005989297,13006321073],p54 [8711488945,13123556817,13123888593,12939343313,4349412817,54382033],p54 [4349212129,4349345249,4315923937,54513121,20825577,20892137],p54 [4399740401,4349476337,20891121,20957681,4181488,4181492]]
private def p1 : List P := [p54 [20956665,20957688,20957692,37666305],p54 [37732865,37733888,20956676],p54 [4181508,37733896]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 7 = true := by decide +kernel
private theorem rows : checks ts 130 21 31 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 8 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one4 8
private def p0 : List P := [p54 [56339488801,56256534581,56340668573,56341207197,56089534745,56090204441],p54 [26007200089,26007666009,26008197465,26008597849,26007593365,26008124821],p54 [26008656277,13006124437,8711292309,12989543861,8694711733,26007921105],p54 [26008518097,13006051793,8711219665,12939343313,4349412817,54447569],p54 [4349212129,4349410785,4315923937,20958689,20891113,20957673],p54 [4181481,4181484,12989471217,8694639089,4399740401,4315921905]]
private def p1 : List P := [p54 [20891121,4180465,4181488,20957684,20823545],p54 [20890105,20956665,20957688,20957692],p54 [37666305,20955649,37733888,4179460],p54 [20957700,54510088]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 4 = true := by decide +kernel
private theorem rows : checks ts 130 24 28 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 9 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one4 9
private def p0 : List P := [p54 [103586098213,52028861601,47734366369,52046753049,47500140825,21713166681],p54 [21713631577,26007793045,21713226133,21713691029,8711092629,8711292309],p54 [8694512053,8694777269,26008186321,21713619409,8711021009,8711286225],p54 [8644311505,4349412817,54447569,4349344225,54378977,4315923937],p54 [20958689,20891113,20957673,4181480,4181484,8694440433],p54 [8644308465,4349409777,54444529,20956657,20957680]]
private def p1 : List P := [p54 [20957684,4179449,20957688,4179452],p54 [20957692,4332498433,37533185,37599745,37666305],p54 [20955649,37733888,20956676],p54 [4181508,54510088]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 1 = true := by decide +kernel
private theorem rows : checks ts 130 27 25 = true := checks_join i27 (checks_join i35 (checks_join i43 (i51)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 10 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one4 10
private def p0 : List P := [p54 [90700871721,43438864549,43439400101,43439847709,43188331805,21713298777],p54 [17418599769,21712828821,17418195349,21713757589,17301421461,8694644149],p54 [4399745461,21713222097,17418654161,8711153105,8711418321,4349279697],p54 [54314449,4315924945,20826585,20893145,4349410785,54445537],p54 [20892129,20958689,20957673,4181480,4181484,8694572529],p54 [4349276657,54311409,4315921905,20956657,20957680]]
private def p1 : List P := [p54 [20957684,20823545,20890105,4179449,4180472],p54 [4181496,37733884,4332564993,37599745],p54 [37666305,20955649,37733888,4179460],p54 [20957700,54510088]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 6 = true := by decide +kernel
private theorem rows : checks ts 130 30 22 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 11 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one4 11
private def p0 : List P := [p54 [77798933549,39143900325,34849336485,39144883485,34598202653,17418267993],p54 [13123567961,17417930133,17418394005,17418792341,13006389653,4399546805],p54 [4399745461,17418323409,17418787281,8711286225,4416453073,4349346257],p54 [4315924945,20826585,20958681,4349477345,20892129,4181473],p54 [4181476,20957673,4181480,4181484,8694705649,4349409777],p54 [20890097,20956657,20957680,20957684]]
private def p1 : List P := [p54 [20890105,4179449,20957688,20956668],p54 [4181500,37599745,37666305,20955649,20956672],p54 [4181504,37733892,20955656],p54 [20957704]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 3 = true := by decide +kernel
private theorem rows : checks ts 130 33 19 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 12 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one4 12
private def p0 : List P := [p54 [65418072113,30554820897,30555418913,30303687065,13123760537,13006389657],p54 [4399612345,4399745465,13106647509,13107044821,4399477205,4399610325],p54 [4399808981,4315924949,20892125,20958685,37734885,4181476],p54 [4181480,4181484,4399673841,4349409777,20824561,20956657],p54 [20957680,20957684,20890105,4179449],p54 [20957688,37733884,37599745]]
private def p1 : List P := [p54 [37666305,20955649,37733888,4179460],p54 [20957700,54510088]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem rows : checks ts 130 36 16 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 13 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one4 13
private def p0 : List P := [p54 [52516068405,51778526497,26008264029,21713697117,25891085721,8711092633],p54 [8711357849,25874570681,8694577593,8644380089,4332570057,37604809],p54 [12989275605,8694509013,8644377045,4349478357,54513109,4332501477],p54 [37536229,37668325,37734885,4181476,4181480,4181484],p54 [12989472241,8694705649,4349409777,54444529,20956657,4180464],p54 [4181488,20957684,4179449,20957688]]
private def p1 : List P := [p54 [37733884,37599745,37666305,20955649],p54 [37733888,37733892],p54 [54510088]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 5 = true := by decide +kernel
private theorem rows : checks ts 130 39 13 = true := checks_join i39 (i47)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤130) (hj : a.j≤51) :
    Covered 14 .one4 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne4
