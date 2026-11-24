import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass17

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group17
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2147552261, 956370953, 6426334217, 2114591757, 2114592781, 1963598861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1711941649, 1527393297, 1393176593, 1258959893, 1158297621, 1074412565], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [990527513, 923419673, 873089049, 805981213, 772427805, 738874397], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [19212621857, 10605915173, 6294173737, 1982431277, 1965655085, 1898547249], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1848216625, 1797886001, 1730778165, 1697224757, 1663671349, 1613340729], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1579787321, 1546233913, 1495903293, 1479127101, 1445573693, 1412020289], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1378466881, 1361690689, 1328137285, 1311361093, 1294584901, 1261031497], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1244255305, 1227479113, 1193925709, 1177149517, 18474423505, 22735835353], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22702279905, 26946914541, 9748156657, 26896581881, 26829472009, 26762362137], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [39564032301, 39463368005, 39345926497, 1100169994603, 1100153216367, 1100136438131], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100119659895, 1100102816123, 1100086037887, 39211707777, 557631873, 3982724], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4819042697, 4802264461, 9063676309, 9046898073, 9013342625, 13291531685], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [39027157421, 13257976237, 17519388085, 17485832637, 17452277189, 21713689037], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8794641877, 8744309217, 38792275429, 12988943853, 12938611193, 12888278533], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6426335241, 2114592781, 1963598861, 1711941649, 1527393297, 1376399377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1225405461, 1124743189, 1040858133, 956973081, 889865241, 822757401], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [772426781, 722096157, 688542749, 19212621857, 10605915173, 1999206441], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1982430253, 1965654061, 1915323437, 1848215601, 1797884977, 1747554353], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1680446517, 1646893109, 1596562485, 1546231865, 1512678457, 1479125049], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428794429, 1412018237, 1378464829, 1344911425, 1311358017, 1294581825], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1261028421, 1244252229, 1210698821, 1177145417, 1160369225, 1143593033], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1126816845, 1110040653, 18524755141, 22786166989, 22735834329, 22702278881], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26930136305, 26863026433, 26795916561, 39597586725, 39496922429, 1100237103451], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [39362703709, 1100220324191, 1100220325215, 1100203545955, 1100186702183, 1100169923947], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100136368499, 1100119590263, 591184249, 574406013, 39211707777, 4835817861], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4819039625, 9080451473, 9063673237, 9030117789, 13291529637, 39027157421], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13257974189, 17519386037, 17469053377, 4550006217, 8794640853, 8744308193], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [38792275429, 8693975533, 12938610169, 12888277509], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1980376077, 1728718865, 1544170513, 1376399377, 1242182677, 1124743189], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1040858133, 940195865, 873088025, 805980185, 738872349, 705318941], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [654988317, 19212621857, 10605915173, 1999206441, 1982430253, 1932099629], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1881769005, 1797883953, 1747553329, 1697222705, 1646892085, 1596561461], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1563008053, 1495900217, 1462346809, 1428793401, 1378462781, 1361686589], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1328133181, 1277802561, 1261026369, 1244250177, 1193919557, 1177143365], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1160367173, 1126813769, 1110037577, 1093261385, 1059707981, 1042931789], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18558309565, 18507976905, 22769388753, 22719056093, 26946913517, 26879803645], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26795916561, 39597586725, 39480145217, 1100304212299, 1100287434063, 1100270655827], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100253877591, 1100119003483, 39362703709, 1100135779679, 1100152555875, 1100186699111], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100153143663, 624737649, 607959413, 4869371261, 39194930565, 4835815813], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4819037577, 9080449425, 9046893977, 13308305825, 13257973165, 39010380209], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17519385013, 4583560641, 4550005193, 8794639829, 8744307169, 38775498217], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099616276975, 8677197297, 1099582721527, 12921831933, 1099549166079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1393176593, 1242182677, 1141520405, 1040858133, 940195865, 873088025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [805980185, 738872349, 688541725, 638211101, 19212621857, 6310947877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6294172713, 1982430253, 1915322413, 1848214573, 1781106737, 1713998897], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1663668273, 1613337653, 1563007029, 1529453621, 1462345785, 1428792377], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1395238969, 1344908349, 1311354941, 1277801533, 1244248129, 1210694721], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1193918529, 1143587909, 1126811717, 1110035525, 1076482121, 1059705929], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1042929737, 1009376333, 992600141, 18575086777, 18524754117, 22769388753], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22719056093, 26946913517, 26879803645, 26795916561, 39580809513, 1100354543935], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [39480145217, 1100337765699, 1100320987463, 1100304209227, 1100119003471, 1100135779667], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100152555863, 1100169332059, 39345926497, 1100169331043, 1100186697063, 641513837], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [624735601, 4886147449, 4852592001, 9114003849, 9080448401, 9046892953], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13291527589, 13257972141, 322147769, 4583559617, 4533226957, 8761084381], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099666608611, 8710751721, 1099633053163, 1099599497715, 12938609145, 1099565942267], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099532386819], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1057635349, 956973081, 873088025, 805980185, 738872349, 688541725], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [638211101, 19212621857, 6310947877, 1999205417, 1999206441, 1965653037], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1898545197, 1831437357, 1764329521, 1697221681, 1646891057, 1579783221], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1546229813, 1495899189, 1445568569, 1395237945, 1361684537, 1311353917], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1277800509, 1244247101, 1210693697, 1177140289, 1160364097, 1110033477], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1093257285, 1059703877, 1026150473, 1009374281, 992598089, 959044685], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [942268493, 18575086777, 18524754117, 22769388753, 22719056093, 26946913517], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26863026433, 26779139349, 1100404875571, 1100388097335, 1100371319099, 1100354540863], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100135780675, 1100152556871, 1100152555855, 1100169332051, 1100169331035, 1100202884447], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100186696039, 658290025, 624734577, 4886146425, 4852590977, 9114002825], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [9063670165, 13325082013, 13274749353, 355702193, 4600336829, 4550004169], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8777861593, 1099700163035, 1099666607587, 8727528933, 1099633052139, 1099599496691], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [12955386357, 1099565941243, 12888276485, 3980804], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [822757401, 755649565, 688541725, 654988317, 19212621857, 6310947877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1999205417, 1999206441, 1965653037, 1898545197, 1831437357, 1747552305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1697221681, 1646891057, 1579783221, 1529452597, 1479121973, 1428791353], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378460729, 1344907321, 1294576701, 1261023293, 1227469885, 1177139265], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143585857, 1126809665, 1076479045, 1059702853, 1026149445, 992596041], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [975819849, 959043657, 925490253, 908714061, 18558309565, 22819721413], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22752611541, 22702278881, 1100438429995, 1100421651759, 1100404873523, 1100388095287], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100135780667, 1100152556863, 1100152555847, 1100186109259, 1100186108243, 1100219661655], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100219660639, 675067237, 641511789, 4902923637, 4869368189, 9130780037], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [9080447377, 9046891929, 13291526565, 355702193, 4600336829, 4550004169], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099733717459, 8794638805, 1099700162011, 1099666606563, 8727528933, 1099616273903], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [12955386357, 1099582718455, 1099532385795, 12888276485], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [654988317, 19212621857, 10605915173, 1999206441, 1982430253, 1898545197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831437357, 1747552305, 1697221681, 1646891057, 1563006005, 1512675381], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1479121973, 1412014137, 1361683513, 1328130105, 1277799485, 1244246077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1210692669, 1160362049, 1126808641, 1093255233, 1059701829, 1026148421], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009372229, 975818825, 942265417, 925489225, 891935821, 875159629], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [18558309565, 1100471984419, 1100455206183, 1100438427947, 1100421649711, 1100135780663], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100152556859, 1100169333055, 1100169332039, 1100202885451, 1100219661651, 1100219660635], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100202882403, 658289001, 624733553, 4886145401, 4852589953, 9097224589], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9046891929, 13308303777, 372479405, 4600336829, 4550004169, 1099750494671], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8794638805, 1099716939223, 1099683383775, 8727528933, 1099649828327, 1099599495667], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [12955386357, 1099549163007, 3979780], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14917656609, 6294171689, 1999206441, 1982430253, 1915322413, 1848214573], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764329521, 1697221681, 1646891057, 1563006005, 1512675381, 1462344757], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1412014137, 1361683513, 1328130105, 1261022269, 1227468861, 1193915453], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1143584833, 1110031425, 1076478017, 1042924613, 1009371205, 992595013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942264393, 925488201, 908712009, 858381389, 841605197, 1100488761627], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488760607, 1100455205159, 1100438426923, 1100152557871, 1100152556855, 1100169333051], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100186109251, 1100202885447, 1100219661647, 1100236437847, 1100219659615, 675066213], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [641510765, 4886145401, 4852589953, 9097224589, 9063669141, 13308303777], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [372479405, 4600336829, 4550004169, 1099767271883, 1099733716435, 8777861593], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099700160987, 1099649828327, 8710751721, 1099616272879, 12938609145, 1099565940219], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [3979780, 4121092], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 129 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10605915173, 1999206441, 1982430253, 1932099629, 1848214573, 1764329521], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1713998897, 1646891057, 1579783221, 1512675381, 1479121973, 1412014137], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1361683513, 1311352889, 1261022269, 1227468861, 1193915453, 1143584833], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1110031425, 1076478017, 1026147397, 992593989, 975817797, 925487177], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [908710985, 875157577, 841604173, 824827981, 1100488761623, 1100505537819], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488759583, 1100455204135, 1100152557867, 1100152556851, 1100186110263, 1100186109247], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100202885447, 1100219661647, 1100219660631, 1100219659615, 675066213, 641510765], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4902922613, 4852589953, 9097224589, 9046891929, 13308303777, 355702193], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4600336829, 1099784049095, 4533226957, 1099750493647, 8777861593, 1099700160987], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099666605539, 8710751721, 1099616272879, 1099565940219, 12921831933, 1099532384771], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099532526083], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1999206441, 1982430253, 1948876845, 1864991789, 1781106737, 1713998897], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1663668273, 1579783221, 1529452597, 1479121973, 1412014137, 1361683513], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1328130105, 1261022269, 1227468861, 1177138237, 1126807617, 1093254209], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059700801, 1026147397, 992593989, 959040581, 925487177, 891933769], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [875157577, 824826957, 808050765, 1100505538835, 1100522315031, 1100488759583], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100471981347, 1100135780651, 1100169334063, 1100169333047, 1100186109247, 1100219662659], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100219661643, 1100236437843, 1100236436827, 675066213, 641510765, 4886145401], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4852589953, 9097224589, 9046891929, 13291526565, 355702193, 4583559617], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099800826307, 4533226957, 1099750493647, 1099716938199, 8761084381, 1099666605539], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8693974509, 1099616272879, 1099582717431, 12905054721, 1099532384771, 1099532526083], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1881769005, 1797883953, 1730776113, 1663668273, 1596560437, 1529452597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1479121973, 1412014137, 1361683513, 1328130105, 1261022269, 1227468861], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1193915453, 1126807617, 1093254209, 1059700801, 1009370181, 992593989], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [959040581, 908709961, 891933769, 858380361, 824826957, 791273549], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100522316047, 1100522315031, 1100505536795, 1100471981347, 1100152557863, 1100169334063], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100169333047, 1100202886459, 1100219662659, 1100236438859, 1100253215059, 1100219659615], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [675066213, 4936478061, 4886145401, 4852589953, 9097224589, 9046891929], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13291526565, 338924981, 4583559617, 1099800826307, 1099750493647, 4516449745], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099716938199, 8744307169, 1099666605539, 1099616272879, 8677197297, 1099565940219], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532526083, 3979780], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1680445489, 1596560437, 1546229813, 1495899189, 1428791353, 1378460729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1328130105, 1277799485, 1227468861, 1193915453, 1126807617, 1093254209], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059700801, 1009370181, 975816773, 959040581, 908709961, 875156553], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [858380361, 808049741, 791273549, 1100505538831, 1100539092243, 1100505536795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100488758559, 1100152557863, 1100169334063, 1100186110259, 1100202886459, 1100219662659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100236438859, 1100253215059, 1100219659615, 675066213, 4919700849, 4886145401], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9130780037, 9080447377, 13325082013, 13274749353, 338924981, 1099800826307], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4566782405, 1099750493647, 1099716938199, 1099666605539, 1099616272879, 1099565940219], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099549303295, 3979780], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1495899189, 1428791353, 1378460729, 1344907321, 1277799485, 1227468861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1193915453, 1143584833, 1110031425, 1059700801, 1009370181, 992593989], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [959040581, 908709961, 875156553, 858380361, 808049741, 791273549], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100505538831, 1100539092243, 1100505536795, 1100488758559, 1100152557863, 1100169334063], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100169333047, 1100202886459, 1100219662659, 1100219661647, 1100236437847, 1100219659615], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [675066213, 4919700849, 4869368189, 9130780037, 9080447377, 13325082013], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099800826307, 1099750493647, 1099716938199, 1099666605539, 1099616272879, 1099565940219], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099549303295, 3979780], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 17 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
end Low6960Allocation.Group17
