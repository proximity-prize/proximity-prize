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

namespace Top1
private abbrev P := PaidBatch .two6wide 1
private def p0 : List P := [⟨Compact54Packed.unpack [47734000645,47665724437,95351041061,47483849853,47734930557,47485422777], by decide +kernel⟩,⟨Compact54Packed.unpack [21711883509,21712086261,47737093365,47737826549,43190230261,21712342321], by decide +kernel⟩,⟨Compact54Packed.unpack [21712610609,21715655985,17420956977,21712801133,21713069421,21713861997], by decide +kernel⟩,⟨Compact54Packed.unpack [21714654573,21715447149,21716174189,21598870893,17304237421,8696864141], by decide +kernel⟩,⟨Compact54Packed.unpack [8697260429,8697591181,4402692493,21713259945,21713593769,21714517417], by decide +kernel⟩,⟨Compact54Packed.unpack [21715441065,21716364713,8713373097,8713834921,8714231209,8647190953], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [4352292265,57327017,23708073,23840169,6996401,7062960], by decide +kernel⟩,⟨Compact54Packed.unpack [23839156,4352223673,57258425,23639481,23771577], by decide +kernel⟩,⟨Compact54Packed.unpack [7060921,23839160,40615356], by decide +kernel⟩,⟨Compact54Packed.unpack [23836097,7059905,40615360,7059908], by decide +kernel⟩,⟨Compact54Packed.unpack [40615364,8697054665,8697516489,4352089545], by decide +kernel⟩,⟨Compact54Packed.unpack [57124297,23570889,23702985,23835081,23836104], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [40615368,40613324], by decide +kernel⟩,⟨Compact54Packed.unpack [23839180,23701969,23834065,23835088], by decide +kernel⟩,⟨Compact54Packed.unpack [57391568,23835092], by decide +kernel⟩,⟨Compact54Packed.unpack [57391572,4335508953,40543705], by decide +kernel⟩,⟨Compact54Packed.unpack [23833049,74165720], by decide +kernel⟩,⟨Compact54Packed.unpack [23839192,57388508], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [40615388,40610272], by decide +kernel⟩,⟨Compact54Packed.unpack [74167776], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i3 : checks ts 120 3 8 = true := by decide +kernel
private theorem i11 : checks ts 120 11 8 = true := by decide +kernel
private theorem i19 : checks ts 120 19 8 = true := by decide +kernel
private theorem i27 : checks ts 120 27 8 = true := by decide +kernel
private theorem i35 : checks ts 120 35 8 = true := by decide +kernel
private theorem i43 : checks ts 120 43 7 = true := by decide +kernel
private theorem rows : checks ts 120 3 47 = true := checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 3 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch .two6wide 2
private def p0 : List P := [⟨Compact54Packed.unpack [43438184457,43370955801,91056533545,43440085121,43440030849,43442116857], by decide +kernel⟩,⟨Compact54Packed.unpack [43441997049,43442925817,43190689017,21715983669,17421350197,21712804209], by decide +kernel⟩,⟨Compact54Packed.unpack [17418105201,21714257265,17419754865,21715775857,17421273457,21599198577], by decide +kernel⟩,⟨Compact54Packed.unpack [8714106225,4419207537,8697126289,8697522577,8647325073,4318675345], by decide +kernel⟩,⟨Compact54Packed.unpack [23642521,23709081,4335515041,40484257,40616353,6997409], by decide +kernel⟩,⟨Compact54Packed.unpack [7062948,7062952,21696420269,17401786797,21698069933,17403633069], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [21699850669,17287514541,8697585069,4352158125,57192877,23639469], by decide +kernel⟩,⟨Compact54Packed.unpack [23771565,23838125,23839148,23839152], by decide +kernel⟩,⟨Compact54Packed.unpack [23770549,7059893,40615348,7059896], by decide +kernel⟩,⟨Compact54Packed.unpack [40615352,40348093,40480189,40612285], by decide +kernel⟩,⟨Compact54Packed.unpack [7058877,57391548,7058880], by decide +kernel⟩,⟨Compact54Packed.unpack [57391552,23836100], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [40615364,8697317833,4402419145,4352220617], by decide +kernel⟩,⟨Compact54Packed.unpack [57255369,23701961,23834057,40612296], by decide +kernel⟩,⟨Compact54Packed.unpack [40615368,40612300], by decide +kernel⟩,⟨Compact54Packed.unpack [40615372,6990289,23834064], by decide +kernel⟩,⟨Compact54Packed.unpack [74167760,7055829], by decide +kernel⟩,⟨Compact54Packed.unpack [90942932], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [7062996,40345049,40477145,6989273,23833048], by decide +kernel⟩,⟨Compact54Packed.unpack [90943960], by decide +kernel⟩,⟨Compact54Packed.unpack [6989276,74164700], by decide +kernel⟩,⟨Compact54Packed.unpack [40615388,6989280,23833056], by decide +kernel⟩,⟨Compact54Packed.unpack [90943968], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3
private abbrev ts := tilesOf batches
private theorem i6 : checks ts 120 6 8 = true := by decide +kernel
private theorem i14 : checks ts 120 14 8 = true := by decide +kernel
private theorem i22 : checks ts 120 22 8 = true := by decide +kernel
private theorem i30 : checks ts 120 30 8 = true := by decide +kernel
private theorem i38 : checks ts 120 38 8 = true := by decide +kernel
private theorem i46 : checks ts 120 46 4 = true := by decide +kernel
private theorem rows : checks ts 120 6 44 = true := checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 4 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch .two6wide 3
private def p0 : List P := [⟨Compact54Packed.unpack [86390350861,82466535465,43423114373,39128289413,43441726713,39146967289], by decide +kernel⟩,⟨Compact54Packed.unpack [39147960569,38895853817,17421017397,17421546805,43190986097,38896292209], by decide +kernel⟩,⟨Compact54Packed.unpack [17420810609,17421471089,17304166769,8714237297,4419338609,8697389457], by decide +kernel⟩,⟨Compact54Packed.unpack [4402490769,4352226705,57195921,23642513,23709073,23773593], by decide +kernel⟩,⟨Compact54Packed.unpack [7062937,7062940,40416673,40548769,40615329,7061921], by decide +kernel⟩,⟨Compact54Packed.unpack [7062944,23839140,23839144,21696751021], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [17402248621,17403171245,17404028333,17404819885,8697122221,4402223533], by decide +kernel⟩,⟨Compact54Packed.unpack [4352025005,56994221,4318735789,23770541,7059885,7060908], by decide +kernel⟩,⟨Compact54Packed.unpack [23839148,57391536], by decide +kernel⟩,⟨Compact54Packed.unpack [23637429,23769525,7058869,40614324], by decide +kernel⟩,⟨Compact54Packed.unpack [7062964,74167736], by decide +kernel⟩,⟨Compact54Packed.unpack [4335444413,40413629,40611261,7057853,23836092], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [40615356,40612288], by decide +kernel⟩,⟨Compact54Packed.unpack [40615360,40612292], by decide +kernel⟩,⟨Compact54Packed.unpack [40615364,8697515465,4352154057,23503305], by decide +kernel⟩,⟨Compact54Packed.unpack [23635401,23767497,57388488], by decide +kernel⟩,⟨Compact54Packed.unpack [40615368,40611276], by decide +kernel⟩,⟨Compact54Packed.unpack [57391564,23634385,23766481], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [6990288,74165712], by decide +kernel⟩,⟨Compact54Packed.unpack [23839184,57387476], by decide +kernel⟩,⟨Compact54Packed.unpack [57391572,40278489,40410585], by decide +kernel⟩,⟨Compact54Packed.unpack [23765465,6989272,57387480], by decide +kernel⟩,⟨Compact54Packed.unpack [57391576,6989276,7055836], by decide +kernel⟩,⟨Compact54Packed.unpack [90942940], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [7063004,23765472,40610272], by decide +kernel⟩,⟨Compact54Packed.unpack [74167776], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i9 : checks ts 120 9 8 = true := by decide +kernel
private theorem i17 : checks ts 120 17 8 = true := by decide +kernel
private theorem i25 : checks ts 120 25 8 = true := by decide +kernel
private theorem i33 : checks ts 120 33 8 = true := by decide +kernel
private theorem i41 : checks ts 120 41 8 = true := by decide +kernel
private theorem i49 : checks ts 120 49 1 = true := by decide +kernel
private theorem rows : checks ts 120 9 41 = true := checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 5 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch .two6wide 4
private def p0 : List P := [⟨Compact54Packed.unpack [77799763985,78171765805,39127888009,34833324169,39129460989,34835093757], by decide +kernel⟩,⟨Compact54Packed.unpack [39131380989,34601018621,17404437817,13109803321,39131033969,34601130353], by decide +kernel⟩,⟨Compact54Packed.unpack [17420942705,17421668721,8713905521,4419006833,12942293361,4352162177], by decide +kernel⟩,⟨Compact54Packed.unpack [4352360833,8697587089,4352160145,4318738833,23773585,23840145], by decide +kernel⟩,⟨Compact54Packed.unpack [23640473,23772569,7061913,7062936,23839132], by decide +kernel⟩,⟨Compact54Packed.unpack [4335579553,40614305,7060897,23839136,7060900], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23839140,40615336,17403435437], by decide +kernel⟩,⟨Compact54Packed.unpack [13108932013,17287183789,8697319853,4402421165,4352222637,57257389], by decide +kernel⟩,⟨Compact54Packed.unpack [23703981,23836077,57391532], by decide +kernel⟩,⟨Compact54Packed.unpack [57391536,23835061,7058868], by decide +kernel⟩,⟨Compact54Packed.unpack [57391540,23836088], by decide +kernel⟩,⟨Compact54Packed.unpack [40615352,40347069,40479165,23834045], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [90943932], by decide +kernel⟩,⟨Compact54Packed.unpack [90943936], by decide +kernel⟩,⟨Compact54Packed.unpack [90942916], by decide +kernel⟩,⟨Compact54Packed.unpack [7062980,8696856009,4402022857,8647184841,4318666185,23700937], by decide +kernel⟩,⟨Compact54Packed.unpack [6990281,74165704], by decide +kernel⟩,⟨Compact54Packed.unpack [23839176,6990284,40611276], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [57391564,23502289,23634385], by decide +kernel⟩,⟨Compact54Packed.unpack [6989265,6990288,57388496], by decide +kernel⟩,⟨Compact54Packed.unpack [40615376,6989268,23833044], by decide +kernel⟩,⟨Compact54Packed.unpack [90943956], by decide +kernel⟩,⟨Compact54Packed.unpack [4335243737,40278489,40476121,23765465,6989272,7055832], by decide +kernel⟩,⟨Compact54Packed.unpack [90942936], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [7063000,6989276,57387484], by decide +kernel⟩,⟨Compact54Packed.unpack [57391580,23765472], by decide +kernel⟩,⟨Compact54Packed.unpack [90941920], by decide +kernel⟩,⟨Compact54Packed.unpack [23839200], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i12 : checks ts 120 12 8 = true := by decide +kernel
private theorem i20 : checks ts 120 20 8 = true := by decide +kernel
private theorem i28 : checks ts 120 28 8 = true := by decide +kernel
private theorem i36 : checks ts 120 36 8 = true := by decide +kernel
private theorem i44 : checks ts 120 44 6 = true := by decide +kernel
private theorem rows : checks ts 120 12 38 = true := checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 6 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch .two6wide 5
private def p0 : List P := [⟨Compact54Packed.unpack [73487760405,69581636653,73490709641,34834234621,34835292413,34836350205], by decide +kernel⟩,⟨Compact54Packed.unpack [30305986813,13109406009,13109868857,34835742065,34601394545,17421272433], by decide +kernel⟩,⟨Compact54Packed.unpack [13126703473,13009332593,4351965553,4352164209,4352227713,4318806401], by decide +kernel⟩,⟨Compact54Packed.unpack [23708041,23840137,4402489745,4352225681,4318804369,23839121], by decide +kernel⟩,⟨Compact54Packed.unpack [7062928,7062932,23706009,23838105,23839128], by decide +kernel⟩,⟨Compact54Packed.unpack [23839132,40415649,40547745,23837089,7060896], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [23839136,40615332,7059880], by decide +kernel⟩,⟨Compact54Packed.unpack [40615336,17403765165,13109261741,17287513517], by decide +kernel⟩,⟨Compact54Packed.unpack [4402289069,4402618797,4318734765,23769517,7058861,7059884], by decide +kernel⟩,⟨Compact54Packed.unpack [40615340,40613296], by decide +kernel⟩,⟨Compact54Packed.unpack [23839152,23570869,23702965,7057845,7058868], by decide +kernel⟩,⟨Compact54Packed.unpack [57391540,23835064], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [57391544,40544701,23834045], by decide +kernel⟩,⟨Compact54Packed.unpack [90943932], by decide +kernel⟩,⟨Compact54Packed.unpack [90943936], by decide +kernel⟩,⟨Compact54Packed.unpack [90942916], by decide +kernel⟩,⟨Compact54Packed.unpack [7062980,8697185737,4402352585,4352219593,23568841,23700937], by decide +kernel⟩,⟨Compact54Packed.unpack [6990280,74165704], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [23839176,6990284,40611276], by decide +kernel⟩,⟨Compact54Packed.unpack [57391564,23699921,6989265], by decide +kernel⟩,⟨Compact54Packed.unpack [6990288,74165712], by decide +kernel⟩,⟨Compact54Packed.unpack [23839184,6989268,40610260], by decide +kernel⟩,⟨Compact54Packed.unpack [74167764,40278489], by decide +kernel⟩,⟨Compact54Packed.unpack [40476121,6988249,6989272,40610264], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [74167768,6988252], by decide +kernel⟩,⟨Compact54Packed.unpack [6989276,74164700], by decide +kernel⟩,⟨Compact54Packed.unpack [40615388,23765472,7055840], by decide +kernel⟩,⟨Compact54Packed.unpack [90942944], by decide +kernel⟩,⟨Compact54Packed.unpack [7063008], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i15 : checks ts 120 15 8 = true := by decide +kernel
private theorem i23 : checks ts 120 23 8 = true := by decide +kernel
private theorem i31 : checks ts 120 31 8 = true := by decide +kernel
private theorem i39 : checks ts 120 39 8 = true := by decide +kernel
private theorem i47 : checks ts 120 47 3 = true := by decide +kernel
private theorem rows : checks ts 120 15 35 = true := checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 7 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch .two6wide 6
private def p0 : List P := [⟨Compact54Packed.unpack [65386596377,65286735921,30539204865,30540261633,30541318401,30306183425], by decide +kernel⟩,⟨Compact54Packed.unpack [13109537085,12992035133,4402100569,4402364761,30523804021,30289455477], by decide +kernel⟩,⟨Compact54Packed.unpack [13109332341,13109926261,4402030965,4402360693,4402624885,4352295285], by decide +kernel⟩,⟨Compact54Packed.unpack [40485253,40617349,4402489745,4352291217,23574929,23772561], by decide +kernel⟩,⟨Compact54Packed.unpack [7061905,7062928,23839124,23706009,7060889], by decide +kernel⟩,⟨Compact54Packed.unpack [23839128,40615324,40415649], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [40547745,7059873,40615328,7059876], by decide +kernel⟩,⟨Compact54Packed.unpack [40615332,40614312], by decide +kernel⟩,⟨Compact54Packed.unpack [7062952,13108668845,13109459373,12992285101,4402289069,4402618797], by decide +kernel⟩,⟨Compact54Packed.unpack [4318734765,23769517,7058861,40614316], by decide +kernel⟩,⟨Compact54Packed.unpack [7062956,74167728], by decide +kernel⟩,⟨Compact54Packed.unpack [23570869,23768501,7057845,40613300], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23839156,57389496], by decide +kernel⟩,⟨Compact54Packed.unpack [23839160,40544701,7056829,23835068], by decide +kernel⟩,⟨Compact54Packed.unpack [57391548,23834048], by decide +kernel⟩,⟨Compact54Packed.unpack [74167744,7056836], by decide +kernel⟩,⟨Compact54Packed.unpack [90943940], by decide +kernel⟩,⟨Compact54Packed.unpack [4402022857,4402352585,4352219593,23568841,23700937,6990280], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [90942920], by decide +kernel⟩,⟨Compact54Packed.unpack [7062984,6990284,57388492], by decide +kernel⟩,⟨Compact54Packed.unpack [40615372,23699921,6989265,6990288], by decide +kernel⟩,⟨Compact54Packed.unpack [90942928], by decide +kernel⟩,⟨Compact54Packed.unpack [7062992,6989268,57387476], by decide +kernel⟩,⟨Compact54Packed.unpack [57391572,40278489,40476121], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [23765465,6989272,57387480], by decide +kernel⟩,⟨Compact54Packed.unpack [57391576,6989276,7055836], by decide +kernel⟩,⟨Compact54Packed.unpack [90942940], by decide +kernel⟩,⟨Compact54Packed.unpack [7063004,23765472,40610272], by decide +kernel⟩,⟨Compact54Packed.unpack [74167776], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i18 : checks ts 120 18 8 = true := by decide +kernel
private theorem i26 : checks ts 120 26 8 = true := by decide +kernel
private theorem i34 : checks ts 120 34 8 = true := by decide +kernel
private theorem i42 : checks ts 120 42 8 = true := by decide +kernel
private theorem rows : checks ts 120 18 32 = true := checks_join i18 (checks_join i26 (checks_join i34 (i42)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 8 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch .two6wide 7
private def p0 : List P := [⟨Compact54Packed.unpack [61074658333,56696541233,30539535617,26245297409,26010423553,26011151617], by decide +kernel⟩,⟨Compact54Packed.unpack [25994629437,25877458237,12992294233,8697527641,30524265845,25994491253], by decide +kernel⟩,⟨Compact54Packed.unpack [12991762805,8697061749,4402228597,4402492789,4352228725,57263477], by decide +kernel⟩,⟨Compact54Packed.unpack [40418693,40550789,23840133,7062924,12992156049,8697520529], by decide +kernel⟩,⟨Compact54Packed.unpack [4352159121,4318737809,23772561,7061905,7062928,7061908], by decide +kernel⟩,⟨Compact54Packed.unpack [7062932,23639449,23771545,7060889,23839128], by decide +kernel⟩]
private def p1 : List P := [⟨Compact54Packed.unpack [40615324,40283553,40415649,40547745], by decide +kernel⟩,⟨Compact54Packed.unpack [7059873,40615328,23837092], by decide +kernel⟩,⟨Compact54Packed.unpack [23839140,57391528], by decide +kernel⟩,⟨Compact54Packed.unpack [12991362477,8696726957,4401959341,4402289069,4352090541,57125293], by decide +kernel⟩,⟨Compact54Packed.unpack [23637421,23769517,7058861,40614316], by decide +kernel⟩,⟨Compact54Packed.unpack [7062956,74167728], by decide +kernel⟩]
private def p2 : List P := [⟨Compact54Packed.unpack [23768501,7057845,57390516], by decide +kernel⟩,⟨Compact54Packed.unpack [7062964,74166712], by decide +kernel⟩,⟨Compact54Packed.unpack [7062968,4335509949,40544701,23834045,23835068], by decide +kernel⟩,⟨Compact54Packed.unpack [57391548,23835072], by decide +kernel⟩,⟨Compact54Packed.unpack [57391552,23834052], by decide +kernel⟩,⟨Compact54Packed.unpack [74167748,12991755721], by decide +kernel⟩]
private def p3 : List P := [⟨Compact54Packed.unpack [8697120201,4402352585,4352154057,23568841,23700937,6990280], by decide +kernel⟩,⟨Compact54Packed.unpack [90942920], by decide +kernel⟩,⟨Compact54Packed.unpack [7062984,6990284,57388492], by decide +kernel⟩,⟨Compact54Packed.unpack [40615372,23634385,6989265,6990288], by decide +kernel⟩,⟨Compact54Packed.unpack [90942928], by decide +kernel⟩,⟨Compact54Packed.unpack [7062992,6989268,57387476], by decide +kernel⟩]
private def p4 : List P := [⟨Compact54Packed.unpack [57391572,40212953,40410585], by decide +kernel⟩,⟨Compact54Packed.unpack [23765465,6989272,57387480], by decide +kernel⟩,⟨Compact54Packed.unpack [57391576,6989276,7055836], by decide +kernel⟩,⟨Compact54Packed.unpack [90942940], by decide +kernel⟩,⟨Compact54Packed.unpack [7063004,23765472,40610272], by decide +kernel⟩,⟨Compact54Packed.unpack [74167776], by decide +kernel⟩]
private def batches : List P := p0 ++ p1 ++ p2 ++ p3 ++ p4
private abbrev ts := tilesOf batches
private theorem i21 : checks ts 120 21 8 = true := by decide +kernel
private theorem i29 : checks ts 120 29 8 = true := by decide +kernel
private theorem i37 : checks ts 120 37 8 = true := by decide +kernel
private theorem i45 : checks ts 120 45 5 = true := by decide +kernel
private theorem rows : checks ts 120 21 29 = true := checks_join i21 (checks_join i29 (checks_join i37 (i45)))
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7) (hb : a.b≤120) (hj : a.j≤49) :
    Covered 9 .two6wide a := Compact54Packed.coverAt (bs := batches) rows a ha ht hb hj
end Top7

end Compact50PriceTableTwo6wide
