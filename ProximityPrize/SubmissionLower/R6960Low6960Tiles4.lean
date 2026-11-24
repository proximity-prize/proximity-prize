import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 973148169, 536941577, 2265454601, 2248678413, 1896357901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1611146253, 1393043473, 1258826769, 1141387281, 1023947797, 940062741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [872954901, 805847065, 755516441, 705185817, 19363417117, 10756710433], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [6444968997, 2133226537, 2066118697, 1982233645, 1931903021, 1881572397], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1814464561, 1764133937, 1713803313, 1663472693, 1629919285, 1579588661], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1529258041, 1512481849, 1478928441, 1428597821, 1411821629, 1378268221], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1344714817, 1327938625, 1294385217, 1260831813, 1244055621, 1227279429], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1193726025, 1176949833, 1176950857, 1143397453, 1126621261, 14597428365], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18658773189, 22903407825, 22853075165, 22802742505, 18456187127, 22735567097], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1175663885, 5369966885, 5252525377, 1100354150751, 9413273953, 1100337372515], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100320331111, 1100320332135, 1100303552875, 1100286774639, 1100269996403, 1100253218167], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100236636539, 1100203081091, 1100186302855, 1100169524619, 9211946385, 1100135969171], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100118994327, 1100085438879, 1100051883431, 523477417, 489987505, 4734622141], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [4701066693, 8962478541, 8912145881, 13156780517, 13106447857, 13056115197], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17300749833, 17233639961], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i51 : checks (tilesOf batches) 137 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2265454601, 2248678413, 1929912335, 1611146253, 1393043473, 1242049553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1124610065, 1007170581, 906508309, 839400469, 772292633, 705184793], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [671631385, 19363417117, 10756710433, 2150001701, 2133225513, 2082894889], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2015787049, 1931901997, 1881571373, 1814463533, 1747355697, 1713802289], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1663471665, 1596363829, 1562810421, 1529257013, 1478926393, 1445372985], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1411819577, 1361488957, 1344712765, 1311159357, 1277605953, 1260829761], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1227276353, 1193722949, 1176946757, 1160170565, 1126617161, 1109840969], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1093064777, 1059511373, 1059512397, 18692327613, 18658772165, 22886629589], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22836296929, 22769121521, 1192441097, 5386744097, 5269302589, 1100169338191], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100152561999, 1100186114387, 1100186113367, 1100202889563, 1100219665759, 9413273953], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100236441955, 1100253218151, 1100269994347, 1100269993331, 1100253215095, 1100236633467], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100203078019, 1100186103175, 1100152547727, 9211946385, 1100118992279, 1100085436831], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100051881383, 506698157, 4768175541, 4717842881, 8962477517, 8928922069], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8893178333, 13173556705, 1099632730603, 1099649506799, 13106446833, 1099649505783], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099666281979, 13056114173, 1099666280963, 1099632725515, 57864, 17283971597], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57868, 1099599170067, 16834064, 16834068, 1099565614619, 33610264], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [17216861725, 33610268, 1099532059171, 50386464, 50386468], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
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
private theorem i54 : checks (tilesOf batches) 137 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1627923469, 1409820689, 1258826769, 1124610065, 990393365, 906508309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [839400469, 755515417, 688407577, 638076953, 19363417117, 6461743137], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6444967973, 2133225513, 2066117673, 1982232617, 1898347565, 1848016941], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1780909101, 1713801265, 1663470641, 1613140017, 1562809397, 1512478773], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1478925365, 1428594745, 1395041337, 1361487929, 1311157309, 1294381117], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1260827709, 1227274305, 1193720897, 1176944705, 1143391301, 1126615109], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1093061701, 1059508297, 1042732105, 1042733129, 1009179725, 992403533], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18725882037, 18675549377, 22903406801, 22836296929, 22769121521, 1209218309], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [5386744097, 1100152561983, 5252525377, 1100152560963, 1100202890567, 1100169337159], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100202889547, 1100219665743, 1100219664727, 1100236440923, 1100269994335, 1100286770531], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [9396496741, 1100303546731, 1100286768495, 1100253213047, 1100236434811, 1100202879363], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100169323915, 1100135768467, 9195169173, 1100102213019, 557029793, 506697133], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4768174517, 4717841857, 8962476493, 8912143833, 1099632730587, 1099649506783], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099649505767, 13140001257, 1099649504751, 1099666280947, 13089668597, 1099666279931], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57848, 57852, 1099666278915, 16834048, 17317526021, 16834052], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099632723467, 33610248, 33610252, 50386448, 1099582390807, 50386452], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [17233638937, 67162648, 1099548769823, 67162652, 83938848, 83938852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
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
private theorem i49 : checks (tilesOf batches) 137 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1141387281, 1007170581, 923285525, 839400469, 755515417, 688407577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [638076953, 19363417117, 6461743137, 2150000677, 2150001701, 2116448297], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2049340457, 1965455401, 1881570349, 1814462509, 1764131885, 1680246833], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1629916209, 1579585585, 1529254965, 1478924341, 1445370933, 1395040313], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1361486905, 1327933497, 1277602877, 1244049469, 1210496061, 1176942657], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1143389249, 1126613057, 1093059653, 1076283461, 1042730053, 1009176649], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [992400457, 975624265, 942070861, 942071885, 18725882037, 18675549377], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22903406801, 22836296929, 22752344309, 1192441097, 5369966885, 1100169338163], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100135784755, 1100169337143, 1100186113339, 1100202889535, 1100219665731, 1100219664715], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100236440911, 1100269994323, 1100286770519, 1100303546719, 1100337100131, 1100303544683], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100269989235, 1100236433787, 1100202878339, 1100169322891, 1100135767443, 1100102211995], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [540251557, 506696109, 4751396281, 8996030917, 1099649507787, 1099649506771], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8928921045, 1099666282967, 1099666281951, 8878588385, 1099666280935, 1099666279919], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57836, 13106445809, 57840, 1099666278903, 16834036, 16834040], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099632657919, 33610236, 13039335937, 33610240, 50386436, 1099632656907], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [50386440, 67162636, 1099599101459, 67162640, 17250416149, 83938836], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [83938840, 1099548768799, 1099548837407, 100715036, 100715040, 17183306277], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [100715044], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
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
private theorem i52 : checks (tilesOf batches) 137 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [839400469, 755515417, 705184793, 638076953, 19363417117, 6461743137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2150000677, 2150001701, 2116448297, 2032563241, 1965455401, 1881570349], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1814462509, 1747354669, 1663469617, 1613138993, 1562808369, 1495700533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1462147125, 1411816501, 1361485881, 1327932473, 1294379065, 1244048445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1210495037, 1176941629, 1143388225, 1109834817, 1093058625, 1042728005], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1025951813, 1009175621, 975622217, 958846025, 942069833, 908516429], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [891740237, 18725882037, 18658772165, 22903406801, 22836296929, 1100135784743], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100152560939, 1100169337135, 1100169336115, 1100186112311, 1100202888507, 1100236441919], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100253218115, 1100253217099, 1100286770511, 1100303546711, 1100320322907, 1100337099107], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100303543659, 1100269988211, 1100236432763, 1100202877315, 1100169321867, 1100118989207], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [573805981, 523473321, 4768173493, 1099649507775, 4717840833, 1099649506759], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099649505743, 8945698257, 1099666281939, 1099666280923, 8878588385, 1099666279907], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57824, 57828, 16834024, 1099666278895, 16834028, 13106445809], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [33610224, 1099632657911, 33610228, 50386424, 1099632656895, 50386428], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13039335937, 67162624, 67162628, 1099632655883, 83938824, 83938828], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [17267193361, 83938832, 1099582323223, 1099532060183, 100715028, 100715032], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099548767775, 1099548836383, 117491228, 117491232, 17183306277, 117491236], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
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
private theorem i55 : checks (tilesOf batches) 137 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [654854169, 19363417117, 6461743137, 6444967973, 2133225513, 2049340457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1965455401, 1864793133, 1797685293, 1747354669, 1663469617, 1613138993], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1562808369, 1495700533, 1445369909, 1395039285, 1344708665, 1311155257], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1260824633, 1210494013, 1193717821, 1160164413, 1109833793, 1076280385], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059504193, 1009173573, 992397381, 975621189, 942067785, 908514377], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [891738185, 858184781, 841408589, 18709104825, 1100152561947, 1100152560927], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100169337123, 1100186113319, 1100186112303, 1100202888499, 1100236441911, 1100253218107], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100269994307, 1100286770503, 1100303546703, 1100320322903, 1100337099103, 1100337098083], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100303542635, 1100253209975, 1100219654527, 1100186099079, 1100135766419, 573805981], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [523473321, 4768173493, 1099649507767, 1099666283963, 4717840833, 1099666282947], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099666281931, 8945698257, 1099666280915, 1099666279899, 57816, 8895365597], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57820, 16834016, 1099615881703, 16834020, 33610216, 13123223021], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632657903, 33610220, 50386416, 50386420, 1099632656891, 67162616], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [67162620, 13039335937, 1099632655875, 1099548838403, 83938816, 83938820], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [83938824, 1099615877647, 1099548837391, 100715020, 100715024, 17250416149], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [100715028, 1099565544987, 1099532059163, 117491224, 117491228, 151043616], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [3584548, 151043620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [15068451869, 6444966949, 2150001701, 2133225513, 2049340457, 1965455401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881570349, 1814462509, 1747354669, 1663469617, 1613138993, 1546031153], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1478923317, 1428592693, 1395039285, 1327931449, 1294378041, 1260824633], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1193716797, 1160163389, 1143387197, 1093056577, 1059503169, 1042726977], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [992396357, 975620165, 942066757, 908513353, 891737161, 874960969], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [824630349, 807854157, 1100152561939, 1100152560919, 1100152559903, 1100169336099], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100202889511, 1100219665707, 1100219664691, 1100253218103, 1100253217087, 1100286770499], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100303546699, 1100320322899, 1100353876311, 1100353875295, 1100303542635, 1100269987187], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100236431739, 1100186099079, 1100152543631, 590583193, 540250533, 1099649507759], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099666283955, 4768173493, 1099666282939, 4717840833, 1099666281923, 1099649503695], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8945698257, 57808, 1099666279895, 57812, 16834008, 1099632658911], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [16834012, 8878588385, 33610208, 33610212, 1099615880683, 50386408], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386412, 13106445809, 1099632656883, 67162608, 67162612, 67162616], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099632655871, 1099532061183, 83938812, 13039335937, 83938816, 1099548837383], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715012, 1099632654859, 100715016, 100715020, 134267408, 17250416149], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099582322199, 1099532059159, 117491220, 117491224, 151043612, 1099531989539], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [151043616, 151043620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [10756710433, 2150001701, 2133225513, 2066117673, 1982232617, 1881570349], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1814462509, 1747354669, 1663469617, 1613138993, 1546031153, 1478923317], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1428592693, 1395039285, 1327931449, 1277600825, 1244047417, 1193716797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160163389, 1126609981, 1076279361, 1042725953, 1025949761, 975619141], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942065733, 925289541, 891736137, 858182729, 841406537, 807853133], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [791076941, 1100135784719, 1100152560915, 1100169337111, 1100186113307, 1100186112291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100219665703, 1100236441899, 1100253218099, 1100253217083, 1100286770495, 1100303546695], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100320322895, 1100337099095, 1100353875295, 1100320319847, 1100286764399, 1100236431739], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100186099079, 1100152543631, 590583193, 540250533, 1099649507751, 1099649506735], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4768173493, 1099649505719, 1099666281919, 4717840833, 1099666280903, 57800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57804, 8945698257, 1099666279891, 16834000, 16834004, 1099632658907], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610200, 33610204, 8878588385, 33610208, 1099615880679, 50386404], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386408, 1099632656879, 67162604, 13106445809, 67162608, 67162612], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099632655867, 1099532061179, 83938808, 83938812, 1099548837379, 100715008], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13022558725, 1099649432071, 100715012, 100715016, 134267404, 1099599099411], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [134267408, 3654164, 117491220, 17233638937, 151043608, 1099548766751], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [151043612, 151043616, 151043620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 137 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [2150001701, 2133225513, 2082894889, 1999009833, 1898347565, 1831239725], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764131885, 1680246833, 1613138993, 1562808369, 1478923317, 1428592693], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395039285, 1327931449, 1277600825, 1244047417, 1193716797, 1143386173], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1109832765, 1059502145, 1042725953, 1009172545, 958841925, 942065733], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [908512325, 874958921, 841405513, 824629321, 791075917, 774299725], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099648393483, 1100152560911, 1100169337107, 1100186113303, 1100186112287, 1100219665699], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100219664683, 1100253218095, 1099984789807, 1100269994295, 1100286770495, 1100320323907], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337100107, 1100353876307, 1100353875295, 1100320319847, 1100286764399, 1100236431739], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100186099079, 1100152543631, 590583193, 1099649507747, 523473321, 1099649506731], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099649505715, 4768173493, 1099666281915, 1099666280899, 8996030917, 57796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57800, 1099666279887, 16833996, 16834000, 8928921045, 1099632658903], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610196, 33610200, 33610204, 1099632657891, 50386400, 8861811173], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386404, 67162600, 1099632656879, 67162604, 67162608, 13089668597], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099548838391, 83938804, 1099632655867, 83938808, 83938812, 1099548837379], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715008, 1099632654855, 100715012, 13005781513, 100715016, 134267404], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099599099411, 134267408, 3654164, 117491220, 151043608, 17216861725], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099548766751, 151043612, 151043616, 167819812], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2015787049, 1915124781, 1831239725, 1764131885, 1680246833, 1629916209], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1562808369, 1495700533, 1445369909, 1395039285, 1327931449, 1277600825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1244047417, 1193716797, 1143386173, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [992395329, 958841925, 925288517, 891735109, 858181705, 824628297], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [807852105, 774298701, 757522509, 1099631616263, 1099648392459, 1100169337103], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100186113299, 1100202889499, 1100219665695, 1100236441895, 1100001567015, 1100236440879], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100001565999, 1100269994291, 1100286770491, 1100303546691, 1100337100107, 1100353876307], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100353875295, 1100320319847, 1100286764399, 1100236431739, 1100186099079, 1100135766419], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [573805981, 1099649507743, 1099649506727, 523473321, 1099615885743, 1099666281911], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4751396281, 1099666280899, 57792, 8996030917, 57796, 1099632659915], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099548842443, 16833992, 16833996, 16834000, 8928921045, 1099632658903], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610196, 33610200, 1099632657887, 50386396, 50386400, 13156778469], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386404, 1099649434091, 1099532062187, 67162600, 67162604, 83938800], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099649433079, 1099532061175, 83938804, 13072891385, 83938808, 117491196], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099649432067, 1099532060163, 100715008, 100715012, 117491208, 12989004301], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [134267404, 1099599099411, 134267408, 134267412, 151043608, 1099548766751], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [151043612, 151043616, 167819812], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1780909101, 1697024049, 1629916209, 1579585585, 1495700533, 1445369909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1395039285, 1327931449, 1294378041, 1244047417, 1193716797, 1143386173], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1109832765, 1059502145, 1025948737, 992395329, 942064709, 925288517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [891735109, 841404489, 824628297, 807852105, 757521485, 740745293], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099648393475, 1099648392455, 1100152559887, 1100186113299, 1100202889495, 1100219665695], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100219664679, 1099984789799, 1100253218091, 1100001565995, 1100269994291, 1100286770491], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100320323907, 1100337100107, 1100370653523, 1100353875295, 1100320319847, 1100269987187], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100236431739, 1100186099079, 1100135766419, 1099649507739, 573805981, 1099666283939], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632662955, 506696109, 1099666281911, 4751396281, 1099666280895, 57788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57792, 57796, 8979253705, 1099632659915, 1099532065227, 16833992], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833996, 1099632658899, 33610192, 33610196, 8912143833, 33610200], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632657887, 50386396, 50386400, 67162596, 1099649434091, 1099532062187], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162600, 67162604, 1099548838387, 83938800, 1099649433079, 83938804], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938808, 117491196, 1099532060163, 100715008, 1099632654855, 100715012], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [117491208, 134267404, 1099599099411, 134267408, 134267412, 151043608], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [151043612, 1099531989539, 151043616, 167819812], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1579585585, 1512477749, 1462147125, 1411816501, 1344708665, 1294378041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1244047417, 1193716797, 1160163389, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [992395329, 942064709, 925288517, 891735109, 841404489, 824628297], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [791074889, 757521485, 723968077, 1099648393471, 1099648392455, 1099648391435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100186113299, 1100202889495, 1100219665695, 1100001567011, 1100219664679, 1100253218091], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100001565995, 1100018342191, 1100269994291, 1100303547707, 1100320323907, 1100337100107], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100353876311, 1100353875295, 1100320319847, 1100269987187, 1100219654527, 1100169321867], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [590584213, 1099649507739, 557028769, 1099649506723, 1099615885739, 506696109], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099666281911, 1099666280895, 57788, 57792, 1099548842439, 16833988], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099615882699, 16833992, 16833996, 1099632658899, 33610192, 33610196], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610200, 1099632657887, 50386396, 50386400, 1099548839399, 67162596], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099649434091, 67162600, 67162604, 1099548838387, 83938800, 83938804], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632655867, 83938808, 117491196, 1099532060163, 100715008, 1099649432071], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [100715012, 117491208, 134267404, 1099599099411, 134267408, 134267412], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043608, 151043612, 1099531989539, 151043616, 3578404, 151043620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1411816501, 1344708665, 1294378041, 1260824633, 1193716797, 1160163389], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1126609981, 1059502145, 1025948737, 992395329, 942064709, 925288517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [891735109, 841404489, 824628297, 791074889, 757521485, 723968077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099648393471, 1099631615239, 1099648391435, 1100186113299, 1100202889495, 1100219665695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099984789795, 1100236441895, 1100018343207, 1100269995307, 1100018342191, 1100286771507], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100303547707, 1100320323907, 1100337100111, 1100353876311, 1100353875295, 1100303542635], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [557032817, 573809021, 573808009, 1099666284951, 1099649506723, 1099615885739], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099666281911, 1099666280895, 57788, 57792, 1099548842439, 16833988], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632659915, 16833992, 16833996, 33610192, 1099632658903, 33610196], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [33610200, 50386396, 1099632657891, 50386400, 67162596, 1099532062187], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162600, 1099632656879, 67162604, 83938800, 1099532061175, 83938804], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [121021945, 1099632655867, 83938808, 100715004, 1099532060163, 100715008], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099649432071, 100715012, 121020937, 117491208, 134267404, 134267408], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [70688277, 1099582322199, 3654164, 117491220, 42520, 151043608], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [42524, 151043612, 42528, 1099531989539, 151043616, 42532], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [151043620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group4
