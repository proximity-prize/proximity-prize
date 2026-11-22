/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact54Packed

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

namespace Top8
private abbrev P := PaidBatch .two6wide 8
private def p0 : List P := [⟨Compact54Packed.unpack [52012539937,51930436661,51997794453,51998856341,51764027653,25993712901], by decide +kernel⟩,⟨Compact54Packed.unpack [21699277061,25992913213,21698608445,25994695997,21582360893,8697131353], by decide +kernel⟩,⟨Compact54Packed.unpack [8697527641,25993634165,21699394933,12991894901,8697193845,8647061877], by decide +kernel⟩,⟨Compact54Packed.unpack [4352228725,57263477,4335251845,40286597,40418693,40550789], by decide +kernel⟩,⟨Compact54Packed.unpack [23840133,7062924,12992288145,8647124369,4352291217,57325969], by decide +kernel⟩,⟨Compact54Packed.unpack [23772561,7061905,7062928,23839124,7060889], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23839128,40615324,4335248801], by decide +kernel⟩,⟨Compact54Packed.unpack [40283553,40415649,40547745,7059873,23838112], by decide +kernel⟩,⟨Compact54Packed.unpack [7062944,57391524,7059880], by decide +kernel⟩,⟨Compact54Packed.unpack [40615336,25994355117,21582413229,4402091437], by decide +kernel⟩,⟨Compact54Packed.unpack [4402421165,4352222637,57257389,23769517,7058861,7059884], by decide +kernel⟩,⟨Compact54Packed.unpack [40615340,40613296], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23839152,7057845,40613300], by decide +kernel⟩,⟨Compact54Packed.unpack [23839156,57389496], by decide +kernel⟩,⟨Compact54Packed.unpack [23839160,40347069,40479165,23834045,7057852], by decide +kernel⟩,⟨Compact54Packed.unpack [74167740,7057856], by decide +kernel⟩,⟨Compact54Packed.unpack [74167744,7056836], by decide +kernel⟩,⟨Compact54Packed.unpack [90943940], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [8696659401,8697252297,4402484681,4352286153,23700937,6990281], by decide +kernel⟩,⟨Compact54Packed.unpack [90942920], by decide +kernel⟩,⟨Compact54Packed.unpack [7062984,6990284,57388492], by decide +kernel⟩,⟨Compact54Packed.unpack [40615372,23766481,6990288,7056848], by decide +kernel⟩,⟨Compact54Packed.unpack [90943952], by decide +kernel⟩,⟨Compact54Packed.unpack [90941908], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [23839188,40410585,40542681,6989272,7055832], by decide +kernel⟩,⟨Compact54Packed.unpack [90942936], by decide +kernel⟩,⟨Compact54Packed.unpack [7063000,6989276,57387484], by decide +kernel⟩,⟨Compact54Packed.unpack [57391580,6989280,7055840], by decide +kernel⟩,⟨Compact54Packed.unpack [90942944], by decide +kernel⟩,⟨Compact54Packed.unpack [7063008], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i24 : checks ts 120 24 8 = true := by decide +kernel
private theorem i32 : checks ts 120 32 8 = true := by decide +kernel
private theorem i40 : checks ts 120 40 8 = true := by decide +kernel
private theorem i48 : checks ts 120 48 2 = true := by decide +kernel
private theorem rows : checks ts 120 24 26 = true := checks_join i24 (checks_join i32 (checks_join i40 (i48)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 10 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch .two6wide 9
private def p0 : List P := [⟨Compact54Packed.unpack [47700864037,43340307509,47702764693,43408661653,47468932357,21698747653], by decide +kernel⟩,⟨Compact54Packed.unpack [17404179717,21697948989,21698872637,21699665213,17287263549,8697263449], by decide +kernel⟩,⟨Compact54Packed.unpack [4402430297,21698735477,21699724661,8696864117,8697325941,8647193973], by decide +kernel⟩,⟨Compact54Packed.unpack [4352360821,4335383941,40418693,40550789,23840133,7062924], by decide +kernel⟩,⟨Compact54Packed.unpack [8697257361,8647256465,4318737809,23772561,7061905,7062928], by decide +kernel⟩,⟨Compact54Packed.unpack [23839124,23573913,23706009,7060889,7061912], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [7062936,40615324,4335380897,40415649], by decide +kernel⟩,⟨Compact54Packed.unpack [40547745,23837089,40615328,7060900], by decide +kernel⟩,⟨Compact54Packed.unpack [23839140,57391528], by decide +kernel⟩,⟨Compact54Packed.unpack [21699456429,8696661421,8697188781,8647187885,4318669229,57389485], by decide +kernel⟩,⟨Compact54Packed.unpack [7058861,57391532,7058864], by decide +kernel⟩,⟨Compact54Packed.unpack [57391536,23505333,23702965], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [74167732,7058872], by decide +kernel⟩,⟨Compact54Packed.unpack [57391544,4335246781,40281533], by decide +kernel⟩,⟨Compact54Packed.unpack [40479165,23834045,57389500], by decide +kernel⟩,⟨Compact54Packed.unpack [23839164,57389504], by decide +kernel⟩,⟨Compact54Packed.unpack [23839168,57388484], by decide +kernel⟩,⟨Compact54Packed.unpack [40615364,8696989129,8697582025,4352286153], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [57320905,6990281,57388488], by decide +kernel⟩,⟨Compact54Packed.unpack [40615368,6990284,23834060], by decide +kernel⟩,⟨Compact54Packed.unpack [74167756,6990288], by decide +kernel⟩,⟨Compact54Packed.unpack [90942928], by decide +kernel⟩,⟨Compact54Packed.unpack [7062992,74164692], by decide +kernel⟩,⟨Compact54Packed.unpack [40615380,40345049,40542681,6989272], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [90941912], by decide +kernel⟩,⟨Compact54Packed.unpack [23839192,6989276,40610268], by decide +kernel⟩,⟨Compact54Packed.unpack [74167772,6989280], by decide +kernel⟩,⟨Compact54Packed.unpack [90941920], by decide +kernel⟩,⟨Compact54Packed.unpack [23839200], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i27 : checks ts 120 27 8 = true := by decide +kernel
private theorem i35 : checks ts 120 35 8 = true := by decide +kernel
private theorem i43 : checks ts 120 43 7 = true := by decide +kernel
private theorem rows : checks ts 120 27 23 = true := checks_join i27 (checks_join i35 (i43))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 11 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch .two6wide 10
private def p0 : List P := [⟨Compact54Packed.unpack [82063620137,39112636569,39113629849,38878738697,17403650313,17404310793], by decide +kernel⟩,⟨Compact54Packed.unpack [38879721793,17404567873,17287329089,8697328989,4402495837,17403836793], by decide +kernel⟩,⟨Compact54Packed.unpack [17404693881,8697061753,4402228601,8647259513,4318740857,23642497], by decide +kernel⟩,⟨Compact54Packed.unpack [23774593,4335449481,40484233,40616329,7062921,7062924], by decide +kernel⟩,⟨Compact54Packed.unpack [7062928,8697454997,4402621845,4318803349,23838101,7061908], by decide +kernel⟩,⟨Compact54Packed.unpack [7062932,23839128,23639453,23771549,7060892], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23839132,40615328,40547749], by decide +kernel⟩,⟨Compact54Packed.unpack [7059877,40615332,23837096], by decide +kernel⟩,⟨Compact54Packed.unpack [23839144,57391532], by decide +kernel⟩,⟨Compact54Packed.unpack [17387780529,8696991153,4402223537,4352025009,57059761,23571889], by decide +kernel⟩,⟨Compact54Packed.unpack [23769521,7058865,57391536], by decide +kernel⟩,⟨Compact54Packed.unpack [74167732,23702969], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [7057849,74167736], by decide +kernel⟩,⟨Compact54Packed.unpack [90943932], by decide +kernel⟩,⟨Compact54Packed.unpack [4335444417,40479169,23834049,40612288], by decide +kernel⟩,⟨Compact54Packed.unpack [40615360,40612292], by decide +kernel⟩,⟨Compact54Packed.unpack [40615364,40611272], by decide +kernel⟩,⟨Compact54Packed.unpack [57391560,8680541645,4385774029], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [40280525,40478157,6990285,40611276], by decide +kernel⟩,⟨Compact54Packed.unpack [57391564,6990288,7056848], by decide +kernel⟩,⟨Compact54Packed.unpack [90943952], by decide +kernel⟩,⟨Compact54Packed.unpack [90941908], by decide +kernel⟩,⟨Compact54Packed.unpack [23839188,40477145,6989273,23833048], by decide +kernel⟩,⟨Compact54Packed.unpack [90943960], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [6989276,74164700], by decide +kernel⟩,⟨Compact54Packed.unpack [40615388,6989280,23833056], by decide +kernel⟩,⟨Compact54Packed.unpack [90943968], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i30 : checks ts 120 30 8 = true := by decide +kernel
private theorem i38 : checks ts 120 38 8 = true := by decide +kernel
private theorem i46 : checks ts 120 46 4 = true := by decide +kernel
private theorem rows : checks ts 120 30 20 = true := checks_join i30 (checks_join i38 (i46))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 12 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch .two6wide 11
private def p0 : List P := [⟨Compact54Packed.unpack [69178131501,34800895133,30506657949,34819638537,30289602825,13109602625], by decide +kernel⟩,⟨Compact54Packed.unpack [12992231745,4402166109,4402495837,17404298617,13109860729,4402030969], by decide +kernel⟩,⟨Compact54Packed.unpack [4402360697,4402624889,4318740857,23576961,23774593,40550793], by decide +kernel⟩,⟨Compact54Packed.unpack [7062921,7062924,7062928,4402424213,4352291221,23640469], by decide +kernel⟩,⟨Compact54Packed.unpack [23772565,23839124,23839128,23771549], by decide +kernel⟩,⟨Compact54Packed.unpack [7060893,23839132,40615328], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [40350117,40547749,7059877,40615332], by decide +kernel⟩,⟨Compact54Packed.unpack [57391528,23837100], by decide +kernel⟩,⟨Compact54Packed.unpack [23839148,17287251377,4402158001,4402487729,4318669233], by decide +kernel⟩,⟨Compact54Packed.unpack [23703985,7058865,57391536], by decide +kernel⟩,⟨Compact54Packed.unpack [74167732,23505337], by decide +kernel⟩,⟨Compact54Packed.unpack [23637433,23835065,57390520], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [7062968,74167740], by decide +kernel⟩,⟨Compact54Packed.unpack [40413633,40611265,57389504], by decide +kernel⟩,⟨Compact54Packed.unpack [23839168,57389508], by decide +kernel⟩,⟨Compact54Packed.unpack [23839172,57389512], by decide +kernel⟩,⟨Compact54Packed.unpack [23839176,8680080845,4385313229,4385708493,40214989], by decide +kernel⟩,⟨Compact54Packed.unpack [40412621,23767501,57388492], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [40615372,40611280], by decide +kernel⟩,⟨Compact54Packed.unpack [57391568,7055829,7056852], by decide +kernel⟩,⟨Compact54Packed.unpack [90943956], by decide +kernel⟩,⟨Compact54Packed.unpack [40411609,23766489,57387480], by decide +kernel⟩,⟨Compact54Packed.unpack [57391576,23833052], by decide +kernel⟩,⟨Compact54Packed.unpack [90943964], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [6989280,74164704], by decide +kernel⟩,⟨Compact54Packed.unpack [40615392], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i33 : checks ts 120 33 8 = true := by decide +kernel
private theorem i41 : checks ts 120 41 8 = true := by decide +kernel
private theorem i49 : checks ts 120 49 1 = true := by decide +kernel
private theorem rows : checks ts 120 33 17 = true := checks_join i33 (checks_join i41 (i49))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 13 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch .two6wide 12
private def p0 : List P := [⟨Compact54Packed.unpack [56747266097,26212602125,25994571021,13092891973,8798256453,12991631737], by decide +kernel⟩,⟨Compact54Packed.unpack [8696930681,4402163065,4402492793,4352228729,57263481,40418697], by decide +kernel⟩,⟨Compact54Packed.unpack [40550793,23840137,7062928,12992024981,8697389461,4402556309], by decide +kernel⟩,⟨Compact54Packed.unpack [4352357781,23772565,7061909,7062932,23839128], by decide +kernel⟩,⟨Compact54Packed.unpack [7060893,23839132,40615328], by decide +kernel⟩,⟨Compact54Packed.unpack [40482213,23837093,40615332,7060904], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23839144,57391532], by decide +kernel⟩,⟨Compact54Packed.unpack [12992418225,8647254449,23506353,23703985,23836081,7059888], by decide +kernel⟩,⟨Compact54Packed.unpack [40615344,40614324], by decide +kernel⟩,⟨Compact54Packed.unpack [7062964,23637433,23769529,40613304], by decide +kernel⟩,⟨Compact54Packed.unpack [23839160,57390524], by decide +kernel⟩,⟨Compact54Packed.unpack [7062972,4335378881,40413633,40545729,7057857,7058880], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [57391552,23835076], by decide +kernel⟩,⟨Compact54Packed.unpack [57391556,23835080], by decide +kernel⟩,⟨Compact54Packed.unpack [57391560,4385247693,4385642957], by decide +kernel⟩,⟨Compact54Packed.unpack [4335509965,40544717,7056845,40612300], by decide +kernel⟩,⟨Compact54Packed.unpack [40615372,40611280], by decide +kernel⟩,⟨Compact54Packed.unpack [57391568,23834068], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [74167764,40346073], by decide +kernel⟩,⟨Compact54Packed.unpack [40543705,7055833,57388504], by decide +kernel⟩,⟨Compact54Packed.unpack [40615384,40610268], by decide +kernel⟩,⟨Compact54Packed.unpack [74167772,7055840], by decide +kernel⟩,⟨Compact54Packed.unpack [90942944], by decide +kernel⟩,⟨Compact54Packed.unpack [7063008], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i36 : checks ts 120 36 8 = true := by decide +kernel
private theorem i44 : checks ts 120 44 6 = true := by decide +kernel
private theorem rows : checks ts 120 36 14 = true := checks_join i36 (i44)
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 14 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top12

end Compact50PriceTableTwo6wide
