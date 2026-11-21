import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne3wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join)

namespace Top1
private abbrev P := PaidBatch .one3wide 1
private def p0 : List P := [p54 [13019188229,8690670605,21693212689,47698427929,4345367593,4345369641],p54 [8707513385,104004939817,4345367609,4345369657,25887640649,21726963785],p54 [25887771753,26022251657,21727160457,47766454409,26022513865,21727422665],p54 [26039553289,21744396553,47784214793,52079653129,47784961289,26023038285],p54 [21727881549,26023300493,21728078221,47499461005,26024243597,21729545613],p54 [21729879437,21730147725,26023497165,21728274893,21728739789,21729139149]]
private def p1 : List P := [p54 [26024702413,21730004429,21595923917,8710897101,8711096781,8710825453],p54 [8711025133,8711224813,8644119021,4349151741,54186493]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 130 3 8 = true := by decide +kernel
private theorem i11 : checks ts 130 11 8 = true := by decide +kernel
private theorem i19 : checks ts 130 19 8 = true := by decide +kernel
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 2 = true := by decide +kernel
private theorem rows : checks ts 130 3 50 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 2 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one3wide 2
private def p0 : List P := [p54 [47513671689,47715338265,95431915561,47497353293,47766706317,47766587533],p54 [47498795277,47767570701,47767976205,43473348877,47499254093,21727877517],p54 [21728211341,47499594125,21729343885,21729677709,21730011533,17435246989],p54 [21728074189,21728473549,21728872909,21729337805,21729802701,21730202061],p54 [21596056013,8711094733,4416196045,8711023085,8711157229,8644116973],p54 [4315598317,20565493,20632053,4349149693,54184445,20631037]]
private def p1 : List P := [p54 [3854845,3854848,3853829,3854852,20631048]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 130 6 8 = true := by decide +kernel
private theorem i14 : checks ts 130 14 8 = true := by decide +kernel
private theorem i22 : checks ts 130 22 8 = true := by decide +kernel
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 7 = true := by decide +kernel
private theorem rows : checks ts 130 6 47 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 3 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one3wide 3
private def p0 : List P := [p54 [43470693389,43403661341,91120303149,43471479949,43471622285,43472266509],p54 [43472539917,43473009933,43473479949,43473053069,43204563341,21729475981],p54 [17434711437,21730142605,17300832653,8710963629,4415999405,21729071565],p54 [17434372557,21729934797,17435170253,8710826445,8711026125,8711225805],p54 [4349021645,4315598301,20565477,20566501,8711088621,8644048365],p54 [4349149677,54184429,20631021,20632045,3853813,3854836]]
private def p1 : List P := [p54 [20631032,4349081085,54050301,20562429,20628989],p54 [3852797,20631036,37407232],p54 [20562437,3851781,37407236,3851784],p54 [37407240]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 130 9 8 = true := by decide +kernel
private theorem i17 : checks ts 130 17 8 = true := by decide +kernel
private theorem i25 : checks ts 130 25 8 = true := by decide +kernel
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 4 = true := by decide +kernel
private theorem rows : checks ts 130 9 44 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 4 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one3wide 4
private def p0 : List P := [p54 [86421418001,82547147821,43471548561,39176723601,43472335121,39177641233],p54 [39178110225,38909488401,38910143825,43456344465,38909664657,17434576273],p54 [17434909073,17435176337,17301029265,8711094705,4416130481,17417395665],p54 [17417794001,17418192337,17300888017,8711024081,4416125393,8644116945],p54 [4349152721,4349149665,54118881,20565473,20632033,20631017],p54 [3854824,3854828,8694045169,4399146481,8644046321,4349082097]]
private def p1 : List P := [p54 [20496881,20563441,20630001,20631024,3853812],p54 [3854836,20562425,20628985,37407224],p54 [37407228,4332236289,37205505,37272065],p54 [37404161,20627969,54183424],p54 [54183428,20627976],p54 [37407240]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 130 12 8 = true := by decide +kernel
private theorem i20 : checks ts 130 20 8 = true := by decide +kernel
private theorem i28 : checks ts 130 28 8 = true := by decide +kernel
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem i52 : checks ts 130 52 1 = true := by decide +kernel
private theorem rows : checks ts 130 12 41 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 5 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one3wide 5
private def p0 : List P := [p54 [77831289877,78235469873,39159676053,34864981141,39177239825,34882610449],p54 [39178242321,34614587665,34615177553,39161183633,34614633873,17434642833],p54 [17435041169,17435308433,13006062993,12939085233,4349019585,4349152705],p54 [34598249937,17418324433,17301020113,8711156177,4349017553,4349150673],p54 [20565457,20566481,20631001,3854809,3854812,4349148641],p54 [20497889,20564449,3853793,3854816,20631012]]
private def p1 : List P := [p54 [20563433,20629993,20631016,20631020],p54 [8694177265,4399278577,4349014513,54049265,20495857,20562417],p54 [20628977,37407216,20630004],p54 [3854836,20561401,20627961,37406200],p54 [3854840,54183420,4332302849],p54 [37337601,37404161,54182400]]
private def p2 : List P := [p54 [3854848,70959620],p54 [70959624]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 130 15 8 = true := by decide +kernel
private theorem i23 : checks ts 130 23 8 = true := by decide +kernel
private theorem i31 : checks ts 130 31 8 = true := by decide +kernel
private theorem i39 : checks ts 130 39 8 = true := by decide +kernel
private theorem i47 : checks ts 130 47 6 = true := by decide +kernel
private theorem rows : checks ts 130 15 38 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 6 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one3wide 6
private def p0 : List P := [p54 [73536325657,69662249009,73520859289,34865432853,34865966357,34866499861],p54 [30571869461,34866153873,34614766993,17434841489,13140075921,13005862289],p54 [13006128529,13006124465,4348954033,4349087153,4349085121,4315598273],p54 [20499913,20566473,17417727441,13123027409,17418457553,13006054865],p54 [4348884433,4349017553,4315596241,20565457,20632017,20497881],p54 [20564441,20631001,3854808,3854812,4349015521,4349148641]]
private def p1 : List P := [p54 [20563425,20629985,20631008,20631012],p54 [20628969,37407208,20629996],p54 [3854828,4399212017,4399410673,4315526641,20561393,20627953],p54 [54183408,20628980],p54 [20631028,20428281,20560377,20626937,3850745],p54 [54183416,20627964]]
private def p2 : List P := [p54 [37407228,37336577,37403137,3849729],p54 [70959616,3849732],p54 [70959620,3849736],p54 [70959624]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 130 18 8 = true := by decide +kernel
private theorem i26 : checks ts 130 26 8 = true := by decide +kernel
private theorem i34 : checks ts 130 34 8 = true := by decide +kernel
private theorem i42 : checks ts 130 42 8 = true := by decide +kernel
private theorem i50 : checks ts 130 50 3 = true := by decide +kernel
private theorem rows : checks ts 130 18 35 = true := checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 7 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one3wide 7
private def p0 : List P := [p54 [65450759197,65350505525,30570468629,30571001109,30571468053,30319752469],p54 [13123106133,13123306837,30571189649,30319736209,30185854353,13005927825],p54 [12938888593,12939085217,13005591985,13005858225,12938950065,4348954033],p54 [4349087153,4348818881,4348952001,4349085121,4315598273,20565449],p54 [20632009,13122762193,13123093969,13123425745,13006120401,4348949969],p54 [4349083089,4315596241,20630993,3854800,3854804,20563417]]
private def p1 : List P := [p54 [20629977,20631000,20631004,4349081057],p54 [4315594209,20628961,3852769,20631008,3852772],p54 [20631012,20495849,20627945,3851753,3852776],p54 [20631016,54183404],p54 [4399277553,4399410673,4315526641,20561393,3850737,3851760],p54 [37407216,37405172]]
private def p2 : List P := [p54 [20631028,20493817,20560377,20626937,3850744],p54 [54183416,20627964],p54 [37407228,37336577,37403137,3849728],p54 [70959616,3849732],p54 [70959620,3849736],p54 [70959624]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 130 21 8 = true := by decide +kernel
private theorem i29 : checks ts 130 29 8 = true := by decide +kernel
private theorem i37 : checks ts 130 37 8 = true := by decide +kernel
private theorem i45 : checks ts 130 45 8 = true := by decide +kernel
private theorem rows : checks ts 130 21 32 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 8 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one3wide 8
private def p0 : List P := [p54 [60634521633,56256470069,60635635869,56341077149,60384567577,26024385817],p54 [26024786201,30302232921,26007667033,26008132953,25890830681,12989020537],p54 [8694122873,30302626197,26008060309,25890889109,13006059925,8711227797],p54 [12988947893,8694115765,4399217077,4399415733,4349086133,54120885],p54 [37341637,37408197,20632005,3854796,30302953937,25890816465],p54 [13005987281,8711155153,4349016529,4315595217,20564433,3853777]]
private def p1 : List P := [p54 [3854800,20630996,20496857,20563417,20629977],p54 [20631000,20631004,4315527649,20562401],p54 [20628961,37407200,20629988],p54 [3854820,20494825,20561385,20627945,20628968],p54 [20631016,54183404],p54 [12988744177,8693977585,4399078897,4399277553,4349013489,54048241]]
private def p2 : List P := [p54 [20494833,20626929,3850737,37406192],p54 [3854832,70959604],p54 [20560377,3849721,54182392],p54 [3854840,70958588],p54 [3854844,4332301825,37336577,20625921,20626944],p54 [54183424,20626948]]
private def p3 : List P := [p54 [54183428,20625928],p54 [70959624]]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 130 24 8 = true := by decide +kernel
private theorem i32 : checks ts 130 32 8 = true := by decide +kernel
private theorem i40 : checks ts 130 40 8 = true := by decide +kernel
private theorem i48 : checks ts 130 48 5 = true := by decide +kernel
private theorem rows : checks ts 130 24 29 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 9 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one3wide 9
private def p0 : List P := [p54 [52044524581,51961503801,52028796065,52029333665,51794439449,26024452377],p54 [21729754393,26007334233,21712636249,26008199513,21713501529,26007661973],p54 [21713095061,13005595029,8710828437,8711028117,8711227797,12989079989],p54 [8694247861,8644050357,4349151669,54186421,4332240325,37275077],p54 [37341637,37408197,3854789,3854792,3854796,26008055249],p54 [21595851217,13006053841,8644047313,4315528657,54183377,20629969]]
private def p1 : List P := [p54 [3853777,3854800,20630996,4315594201,3852761],p54 [20631000,37407196,4349014497],p54 [54049249,20495841,20562401,3851745,20629984],p54 [3854816,54183396,20561385],p54 [20627945,54183400,3851756],p54 [37407212,8693778929,8694044145,4399210993]]
private def p2 : List P := [p54 [4399344113,4315525617,54114801,20626929,20627952],p54 [37407216,37405172],p54 [20631028,20427257,20493817,3849721,3850744],p54 [54183416,20626940],p54 [54183420,37270017,37336577],p54 [20625921,70958592]]
private def p3 : List P := [p54 [3854848,70958596],p54 [3854852,70957576],p54 [20631048]]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 130 27 8 = true := by decide +kernel
private theorem i35 : checks ts 130 35 8 = true := by decide +kernel
private theorem i43 : checks ts 130 43 8 = true := by decide +kernel
private theorem i51 : checks ts 130 51 2 = true := by decide +kernel
private theorem rows : checks ts 130 27 26 = true := checks_join i27 (checks_join i35 (checks_join i43 (i51)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 10 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one3wide 10
private def p0 : List P := [p54 [94995904553,47733831845,43439335589,47482698013,43188267293,21712370009],p54 [21712769369,21713234265,17418469721,21712763285,21713228181,21596055957],p54 [8711094677,4416195989,8694049205,8694314421,4349018549,54053301],p54 [4315598261,20565437,20631997,4332306885,37341637,37408197],p54 [3854789,3854792,3854796,21713091025,21595984337,8711088593],p54 [4348949969,53984721,4315595217,20629969,20630992]]
private def p1 : List P := [p54 [20630996,20562393,20628953,3852761,3853784],p54 [3854808,37407196,4349081057,54115809],p54 [20562401,3851745,37407200,3851748],p54 [37407204,20627945,20628968],p54 [20631016,54183404],p54 [8693977585,8694242801,4348946929,53981681,20428273,20560369]]
private def p2 : List P := [p54 [20626929,70959600],p54 [70959604,20493817],p54 [20625913,3849721,54182392],p54 [3854840,70958588],p54 [3854844,4332235265,37270017,37336577,20625921,3849728],p54 [70959616,3849732]]
private def p3 : List P := [p54 [70959620,3848712],p54 [87735816]]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 130 30 8 = true := by decide +kernel
private theorem i38 : checks ts 130 38 8 = true := by decide +kernel
private theorem i46 : checks ts 130 46 7 = true := by decide +kernel
private theorem rows : checks ts 130 30 23 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 11 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one3wide 11
private def p0 : List P := [p54 [82093966381,39143769253,39144303781,39144752413,38893235485,17418136921],p54 [17418535257,17417799061,17418262933,17300958613,8711094677,4416195989],p54 [8694181301,4399282613,4349018549,54053301,4315598261,20565437],p54 [20631997,4332306885,37341637,37408197,3854788,3854792],p54 [3854796,17418192337,17301019089,8711155153,4349082065,4315595217],p54 [20629969,20630992,20630996,20562393]]
private def p1 : List P := [p54 [20628953,37407192,20629980],p54 [3854812,4315527649,20562401,3851745,20629984],p54 [3854816,54183396,20494825],p54 [20561385,20627945,54183400],p54 [54183404,8694110705,4399277553],p54 [4349013489,54048241,20560369,20626929,20627952]]
private def p2 : List P := [p54 [37407216,37405172],p54 [20631028,20560377,3849721,20627960],p54 [37407224,37404156],p54 [37407228,4332301825,37336577,20625921],p54 [87735808],p54 [87735812]]
private def p3 : List P := [p54 [87734792],p54 [3854856]]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 130 33 8 = true := by decide +kernel
private theorem i41 : checks ts 130 41 8 = true := by decide +kernel
private theorem i49 : checks ts 130 49 4 = true := by decide +kernel
private theorem rows : checks ts 130 33 20 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 12 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one3wide 12
private def p0 : List P := [p54 [69208870961,34848870569,30554240169,34849853729,30303171873,13123237213],p54 [13123503453,17418064281,13123364249,13006058905,4348888473,4349021593],p54 [4349019561,4349152681,4399216057,4399349177,4349085113,20499897],p54 [20631993,20565441,3854785,3854788,37275081,37407177],p54 [20630985,3854792,3854796,20630992,17401680341],p54 [12989343189,4399412693,4315528661,20563413,3852757,3853780]]
private def p1 : List P := [p54 [3854804,37407192,4315594205,20628957],p54 [37407196,37407200],p54 [37338597,37405157,54183396],p54 [54183400,20628972],p54 [20631020,4399212017,4399410673,20428273,20560369],p54 [20626929,70959600]]
private def p2 : List P := [p54 [70959604,20493817],p54 [20560377,3849721,54182392],p54 [3854840,70958588],p54 [3854844,37336577,20625921,37404160],p54 [37407232,37404164],p54 [37407236,37403144]]
private def p3 : List P := [p54 [54183432]]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 130 36 8 = true := by decide +kernel
private theorem i44 : checks ts 130 44 8 = true := by decide +kernel
private theorem i52 : checks ts 130 52 1 = true := by decide +kernel
private theorem rows : checks ts 130 36 17 = true := checks_join i36 (checks_join i44 (i52))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤130) (hj : a.j≤52) :
    Covered 13 .one3wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableOne3wide
