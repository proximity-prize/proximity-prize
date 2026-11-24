import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 989925385, 6560551945, 2248809485, 2248810509, 2047484943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1779050513, 1594502161, 1443508241, 1309291541, 1208629269, 1107966997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1024081945, 956974105, 906643481, 23658581021, 15035098149, 6428390441], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2116647981, 2099871789, 2032763949, 1965656113, 1915325489, 1864994865], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1797887029, 1764333621, 1730780213, 1663672377, 1630118969, 1596565561], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1563012157, 1529458749, 1495905341, 1462351937, 1428798529, 1412022337], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1378468933, 1361692741, 1328139333, 1294585929, 1277809737, 1261033545], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1244257357, 27047643381, 14144246009, 26997310721, 26930200849, 26863090977], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [31057393977, 30956729681, 30839288173, 1100236839291, 1100236840315, 1100220061055], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100203282819, 1100186504583, 1100152949135, 621817233, 1100136301971, 1100119523735], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100102614427, 1100069058979, 540652965, 507097517, 4768509365, 4751731129], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4732234173, 9013142977, 8979521993, 8929189333, 13190601181, 13157045733], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13106713073, 4480574969, 17351347709, 17301015049, 21545649685, 21478539813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i3 : checks (tilesOf batches) 137 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 137 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 137 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6560552969, 2248810509, 2047484941, 1779050513, 1594502161, 1426731025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1292514325, 1175074837, 1091189781, 990527513, 923419673, 873089049], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23658581021, 10740130853, 6428389417, 2133424169, 2116647981, 2049540141], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1982432301, 1915324465, 1864993841, 1814663217, 1747555381, 1714001973], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1663671349, 1613340729, 1579787321, 1546233913, 1495903293, 1462349885], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1445573693, 1395243073, 1361689665, 1344913473, 1311360069, 1294583877], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1261030469, 1227477065, 1210700873, 1193924681, 1160371277, 22786230509], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [27030865145, 26963755273, 26879868189, 26795981105, 30973506893, 1100320726375], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [30856065385, 1100303948139, 1100287169903, 1100270391667, 1100253613431, 1100220057983], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100203279747, 1100186501511, 1100169723275, 621817233, 1100136167827, 1100102612379], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [574206365, 540650917, 4802062765, 4768507317, 4732234173, 4734886333], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8996298181, 8945965521, 8912410073, 13157044709, 13106712049, 4480574969], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17351346685, 17301014025, 21528871449], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i6 : checks (tilesOf batches) 137 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 137 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 137 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2064262157, 1795827729, 1594502161, 1443508241, 1292514325, 1175074837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1074412565, 973750297, 906642457, 856311833, 23658581021, 10740130853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6428389417, 2133424169, 2083093549, 2015985709, 1948877869, 1881770033], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1831439409, 1764331569, 1714000949, 1663670325, 1613339701, 1563009081], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1529455673, 1495902265, 1445571645, 1412018237, 1378464829, 1344911425], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1311358017, 1294581825, 1244251205, 1227475013, 1210698821, 1177145417], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1160369225, 1143593033, 1110039629, 22803007721, 27047642357, 26980532485], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26896645401, 26795981105, 30973506893, 1100371058011, 1100354279775, 1100337501539], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100320723303, 1100303945067, 30839288173, 1100287166831, 1100270388595, 1100236833147], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100220054911, 1100186499463, 1100169721227, 621817233, 1100136165779, 590982553], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [557427105, 4818838953, 4785217969, 4751662521, 4715456961, 8996297157], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8945964497, 8912409049, 13140266473, 13089933813, 4463797757, 17334568449], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17267458577, 21495316001], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i9 : checks (tilesOf batches) 137 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 137 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 137 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1460285457, 1309291541, 1191852053, 1091189781, 990527513, 906642457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [839534617, 23658581021, 10740130853, 6428389417, 2133424169, 2066316333], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1999208493, 1932100653, 1848215601, 1797884977, 1747554353, 1680446517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1630115893, 1579785269, 1529454649, 1495901241, 1462347833, 1412017213], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1378463805, 1344910397, 1294579777, 1261026369, 1244250177, 1210696773], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1177143365, 1160367173, 1126813769, 1110037577, 1076484169, 1042930765], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22819784933, 27047642357, 26963755273, 26879868189, 26779203893, 1100371057995], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100387834191, 30956729681, 1100387833175, 1100371054939, 1100354276703, 1100337498467], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100303943019, 1100287164783, 30822510961, 1100270386547, 1100236831099, 1100203275651], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100169720203, 1100136164755, 590981529, 557426081, 523805097, 4785216945], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4734884285, 8979518921, 8929186261, 13173820897, 13123488237, 17351345661], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17284235789, 1099565882907, 17217125917, 1099532327459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i12 : checks (tilesOf batches) 137 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 137 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 137 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1091189781, 990527513, 923419673, 856311833, 23658581021, 10740130853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6428389417, 2133424169, 2049539117, 1982431277, 1915323437, 1831438385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1781107761, 1730777137, 1663669301, 1613338677, 1563008053, 1495900217], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1462346809, 1428793401, 1378462781, 1344909373, 1311355965, 1261025345], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1227471937, 1210695745, 1160365125, 1143588933, 1110035525, 1076482121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1059705929, 1042929737, 1009376333, 22803007721, 27030865145, 26963755273], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [26879868189, 1100354280771, 1100387834183, 1100404610379, 1100421386575, 1100404608339], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100371052891, 1100354274655, 1100320719207, 1100303940971, 1100270385523, 1100236830075], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100203274627, 1100169719179, 624535953, 590980505, 557359521, 4801994157], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4751661497, 8996296133, 8945963473, 13190598109, 13140265449, 13073155577], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17301013001, 1099599437327, 17233903129, 1099565881883, 1099532326435, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [856311833, 23658581021, 10740130853, 6428389417, 2133424169, 2049539117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1982431277, 1915323437, 1831438385, 1764330545, 1713999921, 1646892085], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1596561461, 1546230837, 1479123001, 1445569593, 1412016185, 1344908349], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1311354941, 1277801533, 1227470913, 1210694721, 1177141313, 1126810693], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1110034501, 1076481093, 1042927689, 1026151497, 1009375305, 959044685], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [22803007721, 1100371057975, 1100371056959, 1100404610371, 1100421386567, 1100438162763], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100404607315, 1100387829079, 1100354273631, 1100320718183, 1100303939947, 1100270384499], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100236829051, 1100203273603, 1100152940943, 607757717, 574136733, 4818771369], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4768438709, 9013073345, 8962740685, 8912408025, 13140265449, 13073155577], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099582660103, 17301013001, 1099599436303, 17233903129, 1099565880859, 56856], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56860, 1099532325411, 56864, 16833060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19363615773, 10740131877, 2133423145, 2133424169, 2066316333, 1982431277], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1915323437, 1831438385, 1764330545, 1713999921, 1646892085, 1579784245], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546230837, 1479123001, 1428792377, 1395238969, 1328131133, 1294577725], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1261024317, 1210693697, 1177140289, 1160364097, 1110033477, 1076480069], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059703877, 1009373257, 992597065, 975820873, 942267469, 1100354280755], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371056951, 1100404610363, 1100421386559, 1100438162759, 1100438161739, 1100404606291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100371050843, 1100354272607, 1100320717159, 1100287161711, 1100253606263, 1100220050815], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169718155, 624534929, 574136733, 4818771369, 4785215921, 4718106049], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8962740685, 8912408025, 13140265449, 13073155577, 1099582660095, 1099599436295], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17301013001, 1099582658067, 56848, 56852, 1099565879835, 56856], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17217125917, 16833052, 16833056, 3919396, 33609252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15051874337, 6428389417, 2133424169, 2083093549, 1999208493, 1932100653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831438385, 1781107761, 1713999921, 1646892085, 1579784245, 1529453621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1479123001, 1428792377, 1378461753, 1328131133, 1294577725, 1244247101], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1193916481, 1177140289, 1143586881, 1093256261, 1059702853, 1042926661], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [992596041, 975819849, 942266441, 908713037, 1100371057963, 1100387834159], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404610359, 1100421386555, 1100438162755, 1100454938951, 1100421383503, 1100387828055], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100354272607, 1100337494371, 1100303938923, 1100253606263, 1100220050815, 1100186495367], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624534929, 574136733, 4835548581, 4785215921, 9013073345, 8962740685], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8895630813, 13140265449, 1099582660091, 13056378365, 1099582659075, 17284235789], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099582658063, 56844, 56848, 1099582657047, 16833044, 16833048], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833052, 17200348705, 1099532324387, 33609248, 33609252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6445165605, 2133423145, 2133424169, 2083093549, 2015985709, 1932100653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1848215601, 1781107761, 1713999921, 1646892085, 1596561461, 1546230837], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1479123001, 1428792377, 1378461753, 1328131133, 1277800509, 1244247101], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1193916481, 1160363073, 1126809665, 1076479045, 1042925637, 1026149445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975818825, 959042633, 925489225, 891935821, 1100354280743, 1100387834155], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404610355, 1100421386551, 1100438162751, 1100471716163, 1100438160715, 1100404605267], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100371049819, 1100337494371, 1100303938923, 1100270383475, 1100220050815, 1100186495367], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624534929, 574136733, 4818771369, 4768438709, 9013073345, 8962740685], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8895630813, 13123488237, 1099599437299, 13056378365, 1099582659071, 1099582658059], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56840, 56844, 17267458577, 1099599434259, 16833040, 16833044], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833048, 1099549101599, 33609244, 17200348705, 33609248, 33609252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2133424169, 2099870765, 2015985709, 1948877869, 1864992817, 1797884977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1730777137, 1646892085, 1596561461, 1546230837, 1479123001, 1428792377], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1378461753, 1328131133, 1277800509, 1244247101, 1193916481, 1160363073], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1126809665, 1076479045, 1042925637, 1009372229, 975818825, 942265417], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [925489225, 875158605, 1100371057955, 1100371056939, 1100404610351, 1100421386551], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100454939963, 1100471716163, 1100438160715, 1100404605267, 1100371049819, 1100337494371], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100303938923, 1100270383475, 1100220050815, 1100186495367, 624534929, 574136733], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4818771369, 4768438709, 9013073345, 8945963473, 13173820897, 13106711025], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099582660083, 1099599436283, 17334568449, 1099582658055, 56836, 56840], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56844, 17267458577, 1099582657043, 16833040, 16833044, 33609240], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099549101599, 33609244, 33609248, 17183571493, 50385444], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1965655085, 1864992817, 1797884977, 1747554353, 1663669301, 1613338677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1546230837, 1479123001, 1428792377, 1395238969, 1328131133, 1277800509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1244247101, 1193916481, 1160363073, 1126809665, 1076479045, 1042925637], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1009372229, 959041609, 942265417, 908712009, 875158605, 1100354280739], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100387834151, 1100404610351, 1100421386547, 1100438162747, 1100471716163, 1100438160715], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404605267, 1100371049819, 1100337494371, 1100303938923, 1100270383475, 1100220050815], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [658090377, 624534929, 574136733, 4818771369, 4751661497, 8996296133], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8929186261, 13173820897, 1099582660079, 13106711025, 1099582659067, 56832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17317791237, 1099582658055, 56836, 56840, 1099599434255, 16833036], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16833040, 16833044, 1099565878811, 33609240, 33609244, 33609248], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50385444], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1747554353, 1680446517, 1613338677, 1563008053, 1495900217, 1445569593], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1395238969, 1328131133, 1294577725, 1244247101, 1193916481, 1160363073], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1126809665, 1076479045, 1042925637, 1009372229, 959041609, 925488201], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [908712009, 858381389, 1100371057951, 1100387834151, 1100404610347, 1100421386547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100438162747, 1100471716163, 1100438160715, 1100404605267, 1100371049819, 1100337494371], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100303938923, 1100253606263, 1100220050815, 658090377, 607757717, 557359521], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4801994157, 4751661497, 8979518921, 8929186261, 1099582660079, 1099582659067], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099599435267, 56832, 56836, 56840, 1099599434255, 16833036], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16833040, 16833044, 1099565878811, 33609240, 33609244, 33609248], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50385444], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1563008053, 1495900217, 1445569593, 1395238969, 1344908349, 1294577725], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1261024317, 1193916481, 1160363073, 1126809665, 1076479045, 1042925637], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1009372229, 959041609, 925488201, 908712009, 858381389, 1100371057951], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100371056935, 1100404610347, 1100421386547, 1100454939963, 1100471716163, 1100438160715], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100404605267, 1100371049819, 1100337494371, 1100287161711, 1100253606263, 1100203273603], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [658090377, 607757717, 557359521, 4801994157, 1099582660079, 1099599436279], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099599435267, 56832, 56836, 56840, 1099599434255, 16833036], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [16833040, 16833044, 33609240, 1099549101599, 33609244, 33609248], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [50385444], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group14
