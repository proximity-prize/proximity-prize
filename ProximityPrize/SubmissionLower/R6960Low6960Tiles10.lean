import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2181106693, 973148169, 6459692041, 2064063503, 1661411343, 1392976909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1560881169, 1409887249, 1275670545, 1141453845, 1057568789, 973683733], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [906575897, 839468057, 789137433, 738806813, 705253405, 671699997], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [621369377, 604593185, 587816993, 10639336485, 6327595049, 2032629801], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2015853613, 1965522989, 1898415149, 1831307313, 1797753905, 1747423281], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1680315445, 1646762037, 1613208629, 1562878009, 1529324601, 1495771193], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1462217789, 1428664381, 1411888189, 1361557569, 1344781377, 1328005185], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1294451781, 1260898373, 1244122181, 1210568777, 1210569801, 1193793609], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1160240205, 1143464013, 14347100337, 14330322101, 18608511161, 18574955713], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18541400265, 22802812113, 22769256665, 22718924005, 9764999413, 26946781429], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [26896448769, 26812561685, 26728674601, 39496790341, 39396123997, 1100236972387], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100220194151, 1100203415915, 1100186636655, 1100186637679, 1100169858419, 1100152424823], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100119459199, 591053185, 3849604, 4852464009, 4818908561, 9097097621], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [39127687581, 9063542173, 9046763937, 13308175785, 13274620337, 17536032185], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17502476737, 17468921289, 4533096917, 8777731553, 8744176105, 12988810741], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [38725033469, 12921700869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2164725769, 2080840719, 1661411343, 1392976909, 1560881169, 1393110033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1258893329, 1124676629, 1024014357, 956906517, 856244249, 805913625], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [755583001, 688475165, 654921757, 621368349, 571037729, 554261537], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [520708129, 10639336485, 6327595049, 2032629801, 1965521965, 1915191341], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1848083501, 1780975665, 1730645041, 1697091633, 1629983797, 1596430389], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1546099765, 1495769145, 1462215737, 1445439545, 1395108925, 1361555517], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1344779325, 1294448705, 1277672513, 1260896321, 1210565701, 1193789509], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1177013317, 1143459913, 1126683721, 1109907529, 1093131341, 1076355149], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [10119241889, 14380653737, 14363875501, 18625287349, 18591731901, 18558176453], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22802811089, 22752478429, 22702145769, 26913225981, 26846116109, 26745451813], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [39513567553, 1100304081235, 1100287301975, 1100287302999, 1100270523739, 39396123997], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100253745503, 1100236967267, 1100135647591, 1100152423787, 1100152422771, 1100152421751], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [624605561, 3847552, 4869239173, 4835683725, 9097095573, 9080317337], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [39127687581, 13341729185, 13308173737, 13257841077, 17519252925, 4583428553], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4549873105, 8794507741, 8744175081, 12972032505, 1099582589439, 38708256257], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [12921699845, 1099549033991, 3850764], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1409754125, 1577658385, 1409887249, 1258893329, 1124676629, 1024014357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [940129301, 856244249, 789136409, 738805785, 671697949, 621367325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [587813917, 537483297, 520707105, 487153697, 10639336485, 2032627753], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2032628777, 2015852585, 1931967533, 1881636909, 1814529069, 1747421233], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1697090609, 1646759985, 1579652149, 1546098741, 1512545333, 1445437497], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1411884089, 1395107897, 1344777277, 1311223869, 1277670461, 1244117057], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1227340865, 1193787457, 1160234053, 1143457861, 1126681669, 1093128265], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1076352073, 1059575881, 1026022477, 1009246285, 10152796313, 14414208161], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14397429925, 18658841773, 18625286325, 18574953665, 22819588301, 22769255641], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22702145769, 26930003193, 26846116109, 26745451813, 39513567553, 1100371190083], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100354411847, 1100337633611, 1100320855375, 1100304077139, 1100287298903, 1100135647579], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100152423775, 39379346785, 1100169199971, 1100169198955, 1100185975151, 1100169196915], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [624603513, 4886015361, 4852459913, 9130648973, 9097093525, 13341728161], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13308172713, 13274617265, 338792893, 4583427529, 4533094869, 8777729505], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [8710619633, 1099632921075, 1099599365627, 12955254269, 1099565810179, 1099532254731], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [12888144397], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1275670545, 1141453845, 1040791573, 940129301, 856244249, 789136409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [722028569, 654920733, 621367325, 571036701, 520706081, 487152673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [470376481, 10639336485, 2032627753, 2032628777, 1999075369, 1915190317], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1848082477, 1797751853, 1713866801, 1663536177, 1613205553, 1562874933], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1512544309, 1478990901, 1411883065, 1378329657, 1344776249, 1294445629], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1277669437, 1244116029, 1193785409, 1177009217, 1143455809, 1109902405], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1093126213, 1076350021, 1042796617, 1009243209, 992467017, 975690829], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [958914637, 10169573525, 14447762585, 14414207137, 14380651689, 18625286325], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18591730877, 22836365513, 22769255641, 22702145769, 26930003193, 26829338897], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [26728674601, 1100421521719, 1100404742459, 1100404743483, 1100387964223, 39496790341], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100354408775, 1100337630539, 1100135647567, 1100152423763, 1100169199959, 1100169198943], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100202752355, 1100202751339, 1100169195891, 372354421, 4902791549, 4869236101], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [9130647949, 9080315289, 13341727137, 13291394477, 372347317, 4616981953], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [4566649293, 8794506717, 1099683252711, 8744174057, 1099649697263, 1099616141815], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [12972031481, 1099582586367, 12904921609, 1099532253707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [956906517, 856244249, 789136409, 738805785, 671697949, 621367325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [571036701, 520706081, 487152673, 453599265, 10639336485, 2032627753], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2032628777, 1999075369, 1915190317, 1848082477, 1780974637, 1697089585], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1646758961, 1596428337, 1529320501, 1495767093, 1445436469, 1395105849], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1344775225, 1311221817, 1260891197, 1244115005, 1210561597, 1160230977], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1143454785, 1109901377, 1076347973, 1042794565, 1026018373, 992464969], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [975688777, 958912585, 925359181, 908582989, 10186350737, 14447762585], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14414207137, 18675618985, 18625286325, 18574953665, 22819588301, 22769255641], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22702145769, 26913225981, 1100455076139, 1100455075119, 1100438296883, 1100421518647], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100404740411, 1100387962175, 1100152424771, 1100152423755, 1100169199951, 1100169198935], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100202752347, 1100219528547, 1100202750315, 1100185972079, 389130613, 4902790525], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [9147425161, 9113869713, 9063537053, 13324948901, 389124529, 4633759165], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4583426505, 8811283929, 1099716807135, 1099683251687, 8744174057, 1099649696239], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099616140791, 8677064185, 1099565808131, 12904921609, 3847692, 3990028], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [738805785, 671697949, 621367325, 571036701, 520706081, 487152673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [453599265, 10639336485, 2032627753, 2032628777, 1999075369, 1915190317], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1831305261, 1780974637, 1697089585, 1646758961, 1579651121, 1512543285], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1478989877, 1428659253, 1378328633, 1327998009, 1294444601, 1244113981], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1210560573, 1177007165, 1126676545, 1109900353, 1076346945, 1042793541], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1009240133, 992463941, 958910537, 942134345, 925358153, 891804749], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [875028557, 10186350737, 14447762585, 14414207137, 18675618985, 18625286325], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18574953665, 22819588301, 1100455076131, 1100471852327, 1100471851307, 1100455073071], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100438294835, 1100421516599, 1100152424763, 1100152423747, 1100169199943, 1100185976143], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100202752339, 1100219528539, 1100236304739, 1100202749291, 389130609, 4919567737], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4869235077, 9130646925, 9080314265, 13341726113, 405901741, 4633759165], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4583426505, 1099750361559, 4516316633, 1099716806111, 8760951269, 1099683250663], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632918003, 8677064185, 1099599362555, 1099549029895, 1099532395015, 12904921609], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [3989004, 57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [587813917, 520706081, 487152673, 453599265, 10639336485, 2032627753], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2032628777, 2015852585, 1915190317, 1848082477, 1780974637, 1697089585], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1629981745, 1579651121, 1512543285, 1462212661, 1411882037, 1361551417], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1311220793, 1277667385, 1227336765, 1193783357, 1160229949, 1109899329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1093123137, 1059569729, 1009239109, 992462917, 975686725, 925356105], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [908579913, 891803721, 858250317, 841474125, 10186350737, 14447762585], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [14414207137, 18658841773, 1100455076123, 1100471852319, 1100488628515, 1100488627495], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100471849259, 1100438293811, 1100135647543, 1100169200955, 1100169199939, 1100185976139], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100202752335, 1100219528535, 1100236304735, 1100219526503, 1100185971055, 405906805], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4886012289, 9147424137, 9097091477, 13341726113, 405901741, 355569081], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4583426505, 1099783915983, 4516316633, 1099733583323, 1099700027875, 8744174057], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099649695215, 1099616139767, 8677064185, 1099532395007, 1099565807107, 1099549171207], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57860, 57864, 12888144397, 3846668, 3987980, 57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [453599265, 10639336485, 2032627753, 2032628777, 2015852585, 1931967533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1848082477, 1780974637, 1697089585, 1646758961, 1579651121, 1512543285], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462212661, 1411882037, 1361551417, 1311220793, 1277667385, 1210559549], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1177006141, 1143452733, 1093122113, 1076345921, 1042792513, 992461893], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975685701, 942132293, 908578889, 891802697, 858249289, 824695885], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [807919693, 10186350737, 1100471853331, 1100488629527, 1100505405723, 1100505404707], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100488626471, 1100471848235, 1100135647539, 1100169200951, 1100169199935, 1100185976135], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100219529547, 1100236305747, 1100253081947, 1100236303715, 1100185971055, 405906805], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4886012289, 9147424137, 9097091477, 13341726113, 405901741, 4633759165], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4583426505, 1099800693195, 1099750360535, 8811283929, 1099716805087, 8744174057], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099666472427, 1099616139767, 1099532395003, 8660286973, 1099565807107, 1099549171203], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57856, 57860, 1099532392971, 57864, 12888144397, 3846668], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [16834060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 131 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6344371237, 2032628777, 2032629801, 1931967533, 1864859693, 1797751853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1713866801, 1646758961, 1596428337, 1512543285, 1462212661, 1411882037], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1361551417, 1311220793, 1277667385, 1210559549, 1177006141, 1143452733], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1093122113, 1059568705, 1026015297, 992461893, 958908485, 925355077], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [891801673, 875025481, 841472073, 807918669, 791142477, 1100471853327], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488629523, 1100522182935, 1100522181919, 1100505403683, 1100488625447, 1100152424751], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100152423735, 1100185977147, 1100202753347, 1100202752331, 1100219528531, 1100253081947], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100236303715, 1100185971055, 405906805, 4886012289, 9147424137, 9097091477], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13341726113, 389124529, 4633759165, 1099800693195, 4566649293, 1099767137747], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8794506717, 1099716805087, 1099666472427, 8727396845, 1099632916979, 1099532394999], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [12955254269, 1099582584319, 1099549171199, 57852, 57856, 57860], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099532392971, 16834056, 3846668, 16834060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2032629801, 1948744749, 1881636909, 1797751853, 1713866801, 1663536177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1596428337, 1529320501, 1478989877, 1428659253, 1361551417, 1311220793], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1277667385, 1210559549, 1177006141, 1143452733, 1093122113, 1059568705], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1026015297, 975684677, 942131269, 925355077, 875024457, 858248265], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [824694857, 791141453, 774365261, 1100471853323, 1100505406735, 1100522182931], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100538959131, 1100522180895, 1100488625447, 1099715561771, 1100169200947, 1100185977147], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100185976131, 1100202752331, 1100219528531, 1100253081947, 1099934320991, 1100236303715], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100185971055, 405906805, 4886012289, 9130646925, 9080314265, 13324948901], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [389124529, 4616981953, 1099817470407, 4566649293, 1099767137747, 8794506717], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099716805087, 1099683249639, 8710619633, 1099632916979, 1099549172211, 1099582584319], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099532393983, 57852, 12938477057, 57856, 1099549170183, 16834052], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [16834056, 3846668, 16834060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1814529069, 1730644017, 1663536177, 1613205553, 1529320501, 1478989877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1428659253, 1361551417, 1311220793, 1277667385, 1210559549, 1177006141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1143452733, 1093122113, 1059568705, 1026015297, 975684677, 942131269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [908577861, 875024457, 841471049, 824694857, 774364237, 757588045], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100488630535, 1100505406731, 1100522182931, 1100538959127, 1100522180895, 1100505402659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099715561771, 1100169200947, 1100185977147, 1100185976131, 1100202752331, 1100236305747], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253081947, 1099934320991, 1100236303715, 1100185971055, 422684021, 4886012289], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9130646925, 9080314265, 13324948901, 372347317, 4616981953, 1099817470407], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4549872081, 1099767137747, 1099716805087, 8777729505, 1099683249639, 1099632916979], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532394995, 1099549171195, 57848, 57852, 1099565807107, 57856], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099532392967, 16834052, 16834056, 3846668, 3986956, 33610252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1613205553, 1546097717, 1495767093, 1445436469, 1378328633, 1327998009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1277667385, 1227336765, 1177006141, 1143452733, 1093122113, 1059568705], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1026015297, 975684677, 942131269, 908577861, 875024457, 841471049], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [807917641, 774364237, 757588045, 1100488630535, 1100505406731, 1100538960143], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100538959127, 1100522180895, 1100505402659, 1099715561771, 1100169200947, 1100185977147], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100202753347, 1100219529547, 1100236305747, 1100253081947, 1099934320991, 1100219526503], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [405907821, 4919567737, 4869235077, 9113869713, 9063537053, 13308171689], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [372347317, 1099817470407, 1099767137747, 1099716805087, 1099666472427, 1099532394995], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099616139767, 1099549171195, 57848, 57852, 1099565807107, 57856], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532392967, 16834052, 16834056, 3846668, 3986956, 33610252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1445436469, 1378328633, 1327998009, 1294444601, 1227336765, 1193783357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1143452733, 1093122113, 1059568705, 1026015297, 975684677, 942131269], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [908577861, 858247241, 841471049, 807917641, 774364237, 740810829], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100488630531, 1100505406731, 1100538960143, 1100538959127, 1100538958107, 1100505402659], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099715561771, 1100169200947, 1100185977147, 1100202753347, 1100219529547, 1100236305747], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100253081951, 1099934320991, 1100219526503, 405907825, 4919567737, 9164202373], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9113869713, 1099817470407, 1099767137747, 1099716805087, 1099666472427, 1099549172207], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099616139767, 1099549171195, 57848, 57852, 1099565807107, 57856], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099532392967, 16834052, 16834056, 3986956, 33610252], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group10
