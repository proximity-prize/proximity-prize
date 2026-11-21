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

namespace Top1
private abbrev P := PaidBatch .one3 1
private def p0 : List P := [p54 [13019188229,8690670605,21693147153,47698362393,12935302185,8707513385],p54 [104021585961,4345367609,4345369657,13002476617,8707578953,21726963785],p54 [25887771753,26038963337,21743937673,47783166089,26022448333,21727357133],p54 [26039487757,21744331021,47784083725,52079522061,47784830221,26022907217],p54 [21727816017,26023169425,21728012689,47499329937,26024112529,21729414545],p54 [21729682833,21729951121,26023431633,21728209361,47499723217,26024505809]]
private def p1 : List P := [p54 [21729807825,21730207185,21595995601,8711028209,8711162353]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 131 3 8 = true := by decide +kernel
private theorem i11 : checks ts 131 11 8 = true := by decide +kernel
private theorem i19 : checks ts 131 19 8 = true := by decide +kernel
private theorem i27 : checks ts 131 27 8 = true := by decide +kernel
private theorem i35 : checks ts 131 35 8 = true := by decide +kernel
private theorem i43 : checks ts 131 43 8 = true := by decide +kernel
private theorem i51 : checks ts 131 51 2 = true := by decide +kernel
private theorem rows : checks ts 131 3 50 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 2 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .one3 2
private def p0 : List P := [p54 [47513606153,47715272729,95431718953,47497287757,47766640781,47766521997],p54 [47784335629,47784216845,47784622349,43489929485,21727811985,21728145809],p54 [47499463057,21729212817,21729546641,21729880465,17435050385,21728008657],p54 [21728342481,21728741841,21729206737,21729606097,21730005457,21595924945],p54 [17301094865,8710826481,8711026161,8711160305,4349021681,4315532801],p54 [20499977,20566537]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 131 6 8 = true := by decide +kernel
private theorem i14 : checks ts 131 14 8 = true := by decide +kernel
private theorem i22 : checks ts 131 22 8 = true := by decide +kernel
private theorem i30 : checks ts 131 30 8 = true := by decide +kernel
private theorem i38 : checks ts 131 38 8 = true := by decide +kernel
private theorem i46 : checks ts 131 46 7 = true := by decide +kernel
private theorem rows : checks ts 131 6 47 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 3 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .one3 3
private def p0 : List P := [p54 [43487405069,43420373021,91136949293,43471414417,43471556753,43472135441],p54 [43472408849,43472878865,43473283345,43472922001,43204432273,21729344913],p54 [17434580369,21729946001,17435181457,43204825553,21729738193,17435039185],p54 [21595990481,8711029201,4416130513,8710892017,8711091697,8644051441],p54 [4315532785,20499961,20500985,4349084161,54053377,20565505],p54 [20566529,20565513,3789320,3789324]]
private def batches : List P := p0
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 131 9 8 = true := by decide +kernel
private theorem i17 : checks ts 131 17 8 = true := by decide +kernel
private theorem i25 : checks ts 131 25 8 = true := by decide +kernel
private theorem i33 : checks ts 131 33 8 = true := by decide +kernel
private theorem i41 : checks ts 131 41 8 = true := by decide +kernel
private theorem i49 : checks ts 131 49 4 = true := by decide +kernel
private theorem rows : checks ts 131 9 44 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 4 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .one3 4
private def p0 : List P := [p54 [86421286929,82546951213,43471417489,39176592529,43472138513,39177444625],p54 [39177913617,39178382609,43472925073,39178296721,38910002577,17434979729],p54 [17435246993,17434772945,17435171281,17301024209,8711094737,4416196049],p54 [8711024113,4416125425,4349018609,54053361,20499953,20566513],p54 [20565497,3789305,3789308,4315529729,20564481,3788289],p54 [3789312,20565508,20496905,20563465,3787273]]
private def p1 : List P := [p54 [20565512,37341708]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 131 12 8 = true := by decide +kernel
private theorem i20 : checks ts 131 20 8 = true := by decide +kernel
private theorem i28 : checks ts 131 28 8 = true := by decide +kernel
private theorem i36 : checks ts 131 36 8 = true := by decide +kernel
private theorem i44 : checks ts 131 44 8 = true := by decide +kernel
private theorem i52 : checks ts 131 52 1 = true := by decide +kernel
private theorem rows : checks ts 131 12 41 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 5 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .one3 5
private def p0 : List P := [p54 [77831158805,78252116017,39176387733,34881692821,39177108757,34882479381],p54 [39178045717,34883481877,39161052565,34866488725,17434511765,17434844565],p54 [17435177365,13140346261,17418127829,17418460629,8710959573,4416060885],p54 [4348954069,4349087189,4349085157,20499941,20566501,20565485],p54 [20566509,8694378997,4349017589,20432373,20498933,20565493],p54 [3789300,3789304,20497917,20564477,20565500]]
private def p1 : List P := [p54 [20565504,37273093,37339653,20563461,3787268],p54 [20565508,37341704,3786252],p54 [37341708]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 131 15 8 = true := by decide +kernel
private theorem i23 : checks ts 131 23 8 = true := by decide +kernel
private theorem i31 : checks ts 131 31 8 = true := by decide +kernel
private theorem i39 : checks ts 131 39 8 = true := by decide +kernel
private theorem i47 : checks ts 131 47 6 = true := by decide +kernel
private theorem rows : checks ts 131 15 38 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 6 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .one3 6
private def p0 : List P := [p54 [74057533465,69662117937,34882144533,34882612501,34883146005,30588515605],p54 [34866022805,34614635925,17434710421,13139879317,13005665685,13005931925],p54 [13005927861,12938954165,4348888517,4349021637,17417596373,13122830805],p54 [17418260949,13005923797,12938950101,4349019605,4315532757,20499933],p54 [20500957,4348818917,4348952037,4349085157,20499941,20566501],p54 [20565485,3789292,3789296,4399080949,4399214069,4399347189]]
private def p1 : List P := [p54 [4349083125,20497909,20564469,20565492,3788280],p54 [3789304,20563453,37341692,3787264],p54 [20565504,37273093,37339653,20563460],p54 [20565508,54117896],p54 [54117900]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 131 18 8 = true := by decide +kernel
private theorem i26 : checks ts 131 26 8 = true := by decide +kernel
private theorem i34 : checks ts 131 34 8 = true := by decide +kernel
private theorem i42 : checks ts 131 42 8 = true := by decide +kernel
private theorem i50 : checks ts 131 50 3 = true := by decide +kernel
private theorem rows : checks ts 131 18 35 = true := checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 7 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .one3 7
private def p0 : List P := [p54 [65467405341,65367151669,30570337561,30570870041,30571336985,30571738393],p54 [30571058581,30571656597,30185657749,13005731221,13005997461,13005395381],p54 [13005727157,13005993397,12939019701,4348888517,4349021637,13123229141],p54 [13005923797,12939015637,4349019605,4315532757,20499933,20566493],p54 [4348884453,4349017573,4315530725,20565477,3789284,3789288],p54 [20497901,20564461,20565484,20565488]]
private def p1 : List P := [p54 [4399080949,4399214069,4399412725,4315528693,20563445,3787253],p54 [20565492,37341688,20430333],p54 [20496893,3786237,37341692,3786240],p54 [37341696,37338629,20562437,3786244],p54 [37341700,37340680],p54 [3789320,70894092]]
private def batches : List P := p0 ++ p1
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 131 21 8 = true := by decide +kernel
private theorem i29 : checks ts 131 29 8 = true := by decide +kernel
private theorem i37 : checks ts 131 37 8 = true := by decide +kernel
private theorem i45 : checks ts 131 45 8 = true := by decide +kernel
private theorem rows : checks ts 131 21 32 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 8 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch .one3 8
private def p0 : List P := [p54 [60634456097,56256338997,60635504797,56340946077,60384370969,56089877785],p54 [30302101849,26007470425,26007936345,26008336729,30319272341,26024706453],p54 [26025172373,13005863317,8710965653,13006059957,8643987893,4349020613],p54 [54055365,30302822869,26008322517,13005790677,8710958549,4348819925],p54 [4349018581,4315531733,20566485,20498909,20565469,3789277],p54 [3789280,4348951013,4349084133,20498917,3788261,3789284]]
private def p1 : List P := [p54 [20565480,20564461,20565484,3788272],p54 [3789296,12989210101,8643980789,4349082101,20496885,20563445],p54 [37341684,37341688],p54 [20562429,54117884,3786240],p54 [37341696,8627269125,37272069,37338629],p54 [3785221,54117892,3785224]]
private def p2 : List P := [p54 [54117896,20562444],p54 [37341708]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 131 24 8 = true := by decide +kernel
private theorem i32 : checks ts 131 32 8 = true := by decide +kernel
private theorem i40 : checks ts 131 40 8 = true := by decide +kernel
private theorem i48 : checks ts 131 48 5 = true := by decide +kernel
private theorem rows : checks ts 131 24 29 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 9 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .one3 9
private def p0 : List P := [p54 [52044459045,51961372729,52045442209,52045979809,51794308381,51794911517],p54 [51777989981,26008002909,21713370461,26007530905,21712898457,25890824601],p54 [8710831513,8711031193,12988883385,8694051257,8694250937,8644053433],p54 [4332243401,37278153,26007858645,21713291733,13005857237,8711025109],p54 [8644050389,4315531733,20566485,20498909,20565469,3789276],p54 [3789280,4349083109,54117861,20564453,3788261,3789284]]
private def p1 : List P := [p54 [20565480,3787245,20565484,3787248],p54 [20565488,12989276661,8644047349,4315528693,20563445],p54 [37341684,37341688],p54 [20495869,20562429,54117884],p54 [54117888,4332237317,37272069],p54 [37338629,3785221,54117892]]
private def p2 : List P := [p54 [70894088,3785228],p54 [54117900]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 131 27 8 = true := by decide +kernel
private theorem i35 : checks ts 131 35 8 = true := by decide +kernel
private theorem i43 : checks ts 131 43 8 = true := by decide +kernel
private theorem i51 : checks ts 131 51 2 = true := by decide +kernel
private theorem rows : checks ts 131 27 26 = true := checks_join i27 (checks_join i35 (checks_join i43 (i51)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 10 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .one3 10
private def p0 : List P := [p54 [94995773481,47733700773,43439138981,47751461149,43204847901,21713037661],p54 [17418338653,21712632217,21713031577,21595859353,8710898073,4415999385],p54 [8693918137,8694117817,8694383033,4349021625,37211593,37343689],p54 [21712959957,21595853269,8710891989,8711157205,4349018581,54053333],p54 [20499925,20566485,20565469,3789276,3789280,4315529701],p54 [20564453,20565476,20565480,20431341]]
private def p1 : List P := [p54 [20563437,3787245,20565484,20564464],p54 [3789296,8693780981,8694046197,8694311413,4349015541,54050293],p54 [20496885,3786229,37341684,3786232],p54 [37341688,20562429,20563452],p54 [20565500,54117888],p54 [4332303877,37338629,54116868]]
private def p2 : List P := [p54 [3789316,70894088],p54 [70894092]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 131 30 8 = true := by decide +kernel
private theorem i38 : checks ts 131 38 8 = true := by decide +kernel
private theorem i46 : checks ts 131 46 7 = true := by decide +kernel
private theorem rows : checks ts 131 30 23 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 11 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .one3 11
private def p0 : List P := [p54 [82110612525,39143703721,39144172713,39144621345,38893038881,17418005853],p54 [17418338653,17417667993,17418066329,17418464665,8710898073,4416064921],p54 [8694383033,4349021625,37277129,37343689,17418061269,17418459605],p54 [8710958549,4416059861,4349018581,54053333,20499925,3789269],p54 [3789272,20565469,3789276,3789280,4315529701,20564453],p54 [20565476,20565480,20496877,20563437]]
private def p1 : List P := [p54 [3787245,20565484,37341680],p54 [8643980789,4349082101,20496885,3786229,20564468],p54 [3789300,54117880,20562429],p54 [54117884,20563456],p54 [20565504,8627269125,37272069,37338629,3785220],p54 [54117892,20562440]]
private def p2 : List P := [p54 [37341704,37339660],p54 [20565516]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 131 33 8 = true := by decide +kernel
private theorem i41 : checks ts 131 41 8 = true := by decide +kernel
private theorem i49 : checks ts 131 49 4 = true := by decide +kernel
private theorem rows : checks ts 131 33 20 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 12 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .one3 12
private def p0 : List P := [p54 [69712842801,34849657121,30302975265,13123040605,13123306845,17417933209],p54 [13123167641,13123499417,13006128537,4399351225,4349021625,37277129],p54 [37343689,17418260949,13005923797,12939015637,4349085141,20499925],p54 [3789269,3789272,20565469,3789276,3789280,4348884453],p54 [4349083109,20497893,20564453,20565476,3788264],p54 [3789288,20563437,3787245,20565484,3787248]]
private def p1 : List P := [p54 [20565488,4399080949,4399214069,4399412725,20430325],p54 [20496885,3786229,37341684,3786232],p54 [37341688,20495869,20562429,3786236],p54 [37341692,37340672],p54 [3789312,37338629,54116868],p54 [3789316,70894088]]
private def p2 : List P := [p54 [70894092]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 131 36 8 = true := by decide +kernel
private theorem i44 : checks ts 131 44 8 = true := by decide +kernel
private theorem i52 : checks ts 131 52 1 = true := by decide +kernel
private theorem rows : checks ts 131 36 17 = true := checks_join i36 (checks_join i44 (i52))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 13 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch .one3 13
private def p0 : List P := [p54 [56827681845,26007543077,26007943461,26008001889,25890765153,12988889473],p54 [8694057345,25890758045,13005928861,8711096733,12988816829,8693984701],p54 [12989348285,4349020605,54055357,4332308941,37343693,12989013465],p54 [8694181337,4399282649,4349084121,20498905,20565465,3789272],p54 [3789276,20564449,3788257,3789280,20565476],p54 [37208553,37340649,20564457,20565480,3788268]]
private def p1 : List P := [p54 [3789292,37341680,12989144565,8643980789],p54 [4349082101,20496885,3786229,37341684],p54 [54117880,20562429,3786236],p54 [37341692,37340672],p54 [3789312,8627269125,37272069,37338629,3785221,3786244],p54 [37341700,37339656]]
private def p2 : List P := [p54 [20565512,54116876],p54 [3789324]]
private def batches : List P := p0 ++ p1 ++ p2
private abbrev ts := tilesOf batches
private theorem i39 : checks ts 131 39 8 = true := by decide +kernel
private theorem i47 : checks ts 131 47 6 = true := by decide +kernel
private theorem rows : checks ts 131 39 14 = true := checks_join i39 (i47)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13) (hb : a.b≤131) (hj : a.j≤52) :
    Covered 14 .one3 a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top13

end Compact50PriceTableOne3
