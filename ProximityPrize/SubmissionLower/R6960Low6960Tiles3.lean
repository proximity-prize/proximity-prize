import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass3

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 989925387, 536941577, 2282166281, 2064063501, 1661411341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15151342605, 10822824981, 2216116249, 2216117273, 2132232217, 1998015517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1897353245, 1813468189, 1712805921, 1628920865, 1561813025, 1494705189], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1444374565, 1394043941, 1326936105, 1276605481, 1243052073, 1192721453], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1159168045, 1125614637, 1814464561, 1764133937, 1713803313, 1663472693], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1629919285, 1596365877, 1546035257, 1512481849, 1478928441, 1428597821], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1411821629, 1378268221, 1344714817, 1327938625, 1311162433, 1260831813], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1244055621, 1227279429, 1193726025, 1193727049, 1176950857, 1143397453], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1126621261, 14614205581, 18456187131, 9583101245, 13844513093, 13810957645], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13777402197, 18038814045, 1100370862431, 1100354084195, 1100337305959, 807825769], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100320526699, 1100320527723, 1100303486319, 1100286708083, 757493109, 1100269929847], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100236374399, 5002127745, 1100219596163, 1100202817927, 1100186039691, 4951795085], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100152484243, 1100135706007, 9196429721, 1100102150559, 1100068595111, 9129319849], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1100035039663, 1100001484215, 13340400061, 456300989, 422745541, 4684157389], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13256512977, 13172625893, 17366928893, 17249487385], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2282166281, 2097617935, 1678188559, 15151342605, 10822824981, 2216116249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2216117273, 2115455001, 1964461085, 1863798813, 1763136541, 1662474273], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1595366433, 1528258593, 1444373541, 1394042917, 1343712293, 1276604457], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1226273833, 1192720425, 1142389805, 1108836397, 1075282989, 1764132913], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1713802289, 1663471665, 1613141045, 1562810421, 1529257013, 1478926393], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1445372985, 1411819577, 1378266173, 1344712765, 1311159357, 1277605953], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1260829761, 1227276353, 1193722949, 1176946757, 1160170565, 1126617161], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1109840969, 1093064777, 1076288589, 1059512397, 9633432881, 9599877433], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13861289281, 13827733833, 1100253421903, 13794178385, 1100303751507, 1100270198099], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100303750487, 1100320526683, 858157405, 1100186045791, 1100202821987, 1100219598183], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [807824745, 1100236374379, 1100236373363, 5052459381, 1100253149559, 1100253148539], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [5002126721, 1100219593091, 1100186037643, 1100169259407, 9229984145, 1100135703959], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100102148511, 9161613729, 9162874273, 1100068593063, 1100035037615, 9095764401], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [473077177, 439521729, 13306844613, 13206180317, 17400483317, 1099649437187], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57856, 13037149701, 57860, 1099649436171, 16834056, 16834060], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099615880723, 33610256, 17266264597, 50386452, 1099582325275, 50386456], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [67162652, 1099548769827, 67162656, 83938852, 3586600, 83938856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [15151342605, 10822824981, 2216116249, 2216117273, 2098677785, 1964461085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1847021597, 1746359325, 1645697057, 1561812001, 1494704161, 1410819109], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1360488485, 1293380645, 1226272809, 1192719401, 1142388777, 1092058157], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1058504749, 1024951341, 1713801265, 1663470641, 1613140017, 1562809397], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1512478773, 1478925365, 1428594745, 1395041337, 1361487929, 1311157309], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1294381117, 1260827709, 1227274305, 1193720897, 1176944705, 1143391301], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1126615109, 1109838917, 1076285513, 1059509321, 1042733129, 1009179725], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [992403533, 5388797221, 9650209069, 9616653621, 13878065469, 1100102164799], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100118940995, 1100118939975, 13827732809, 1100286973259, 1100303749455, 1100420116819], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100169268563, 1100186044759, 1100202820955, 858156381, 1100219597151, 1100236373347], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100253149547, 791046509, 1100286702959, 1100269924727, 5035681145, 1100253146491], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100219591043, 4968571273, 1100186035595, 1100152480147, 9196428697, 1100118924699], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100085369251, 9112541613, 523408813, 489853365, 13323621825, 4734488001], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099649442255, 1099649441239, 13222957529, 1099666217435, 1099666214387, 57840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17400483317, 57844, 1099666213371, 16834040, 16834044, 1099666212355], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [33610240, 50386436, 1099649434123, 50386440, 67162636, 17283041809], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099615878675, 67162640, 67162644, 83938840, 1099565546015, 83938844], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [100715040, 100715044, 3585576, 117491240], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [10839601169, 6527859733, 2216117273, 2115455001, 1964461085, 1847021597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1746359325, 1645697057, 1561812001, 1477926945, 1394041893, 1343711269], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1276603429, 1209495593, 1159164969, 1125611561, 1058503725, 1024950317], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [991396909, 1697024049, 1646693425, 1596362801, 1529254965, 1478924341], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1445370933, 1395040313, 1361486905, 1327933497, 1277602877, 1244049469], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1227273277, 1176942657, 1160166465, 1126613057, 1093059653, 1076283461], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1059507269, 1009176649, 992400457, 975624265, 958848077, 942071885], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [5422351645, 9683763493, 9650208045, 1100102164787, 1100135717175, 1100102163767], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13894842681, 1100152493371, 1100169269567, 13861287233, 1100169268551, 1100186044747], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100436894031, 1100202820943, 1100219597139, 874933593, 1100219596123, 1100253149535], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100269925735, 807823721, 1100303479147, 1100286700915, 5052458357, 1100253145467], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100219590019, 4985348485, 1100186034571, 1100152479123, 9196428697, 1100118923675], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100068591015, 9112541613, 506630577, 456297917, 13323621825, 1099649442243], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099649441223, 1099649440207, 1099649439191, 13222957529, 1099649438175, 1099649437159], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57828, 16834024, 1099666213359, 16834028, 33610224, 17400483317], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099666212343, 33610228, 50386424, 1099682988543, 50386428, 67162624], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099666210311, 67162628, 83938824, 83938828, 1099615877651, 83938832], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [17266264597, 100715028, 100715032, 1099565544991, 117491228, 117491232], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [117491236, 3584552, 134267432], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [6527859733, 2216117273, 2132232217, 1981238301, 1863798813, 1763136541], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1645697057, 1561812001, 1477926945, 1394041893, 1326934053, 1276603429], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1209495593, 1159164969, 1108834345, 1041726509, 1008173101, 974619693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1680246833, 1613138993, 1562808369, 1512477749, 1462147125, 1411816501], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1361485881, 1327932473, 1294379065, 1244048445, 1210495037, 1176941629], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1143388225, 1109834817, 1093058625, 1059505221, 1025951813, 1009175621], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [975622217, 958846025, 942069833, 908516429, 891740237, 5439128857], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9700540705, 1100102164775, 9666985257, 1100102163755, 1100118939951, 1100135716147], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13911619893, 1100152492343, 1100169268539, 1100186044735, 13861287233, 1100186043719], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100219597131, 1100436894031, 1100236373327, 1100253149527, 874933593, 1100286702939], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100286701923, 824600933, 1100320255339, 1100286699891, 5052458357, 1100253144443], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100219588995, 4985348485, 1100186033547, 1100135700887, 9196428697, 1100085368227], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [540185001, 9112541613, 489852341, 1099649442231, 1099649441211, 1099649440195], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13306844613, 1099649439179, 1099666215379, 1099666214363, 57816, 13206180317], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [16834012, 1099666213347, 16834016, 33610212, 1099682989547, 33610216], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [50386412, 50386416, 1099666211319, 50386420, 17383706105, 67162616], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099682987519, 67162620, 83938816, 83938820, 1099649432075, 100715016], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [100715020, 100715024, 1099599099415, 117491220, 17249487385, 117491224], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [1099565543967, 134267420, 134267424, 134267428, 151043624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [2149009433, 1998015517, 1880576029, 1779913757, 1662474273, 1578589217], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1494704161, 1394041893, 1326934053, 1276603429, 1192718377, 1142387753], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1092057129, 1041726509, 991395885, 957842477, 1663469617, 1613138993], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1562808369, 1495700533, 1445369909, 1395039285, 1344708665, 1311155257], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1277601849, 1227271229, 1193717821, 1160164413, 1109833793, 1093057601], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1059504193, 1025950789, 992397381, 975621189, 942067785, 925291593], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [891738185, 858184781, 841408589, 5455906069, 1100102164763, 9717317917], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100118940959, 1100135717155, 9666985257, 1100135716139, 1100152492335, 13928397105], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100169268531, 1100186044727, 13878064445, 1100186043711, 1100219597123, 1100453671243], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100219596107, 1100253149519, 1100269925719, 874933593, 1100286701919, 824600933], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100303478119, 1100303477103, 5052458357, 1100269921655, 1100236366207, 1100202810759], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4968571273, 1100152478099, 9179651485, 1100102145439, 540185001, 1099649442219], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [9095764401, 1099649441203, 489852341, 1099649440187, 1099649439171, 13290067401], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099649438155, 57804, 1099666214355, 57808, 16834004, 1099666213339], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [16834008, 33610204, 13189403105, 1099682989539, 33610208, 50386404], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [50386408, 1099666211311, 67162604, 67162608, 1099682987511, 67162612], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [83938808, 17366928893, 83938812, 1099682986499, 100715008, 100715012], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [100715016, 1099632653839, 117491212, 117491216, 134267412, 1099582255643], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [134267416, 17232710173, 134267420, 151043616, 1099531922983, 151043620], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [151043624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1796690973, 1679251489, 1578589217, 1511481377, 1410819109, 1343711269], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1276603429, 1209495593, 1142387753, 1092057129, 1041726509, 991395885], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [957842477, 1663469617, 1613138993, 1546031153, 1478923317, 1445369909], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1395039285, 1327931449, 1294378041, 1260824633, 1210494013, 1176940605], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143387197, 1093056577, 1059503169, 1042726977, 992396357, 975620165], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [942066757, 908513353, 891737161, 874960969, 841407565, 807854157], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100102164755, 5455906069, 1100102163739, 9717317917, 1100118939935, 1100135716131], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100152492327, 9666985257, 1100169268523, 13928397105, 1100169267507, 1100202820919], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13878064445, 1100202819903, 1100236373315, 1100253149515, 925266253, 1100269925715], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [874933593, 1100286701915, 1100303478115, 5102791017, 1100320254315, 1100286698867], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [5035681145, 1100253143419, 1100202810759, 4951794061, 1100152478099, 1100118922651], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [9179651485, 1099649442211, 556962213, 1099649441195, 1099649440179, 9078987189], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [489852341, 1099649439163, 1099666215363, 57796, 1099666214347, 57800], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13273290189, 16833996, 1099682990547, 16834000, 33610196, 33610200], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099666212319, 50386396, 50386400, 1099682988519, 50386404, 67162600], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [67162604, 1099682987507, 83938800, 83938804, 83938808, 1099682986495], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [100715004, 100715008, 117491204, 1099649431051, 117491208, 117491212], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [134267408, 1099599032855, 134267412, 134267416, 151043612, 1099548700195], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [151043616, 151043620, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1511481377, 1427596325, 1360488485, 1293380645, 1209495593, 1159164969], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1108834345, 1041726509, 991395885, 957842477, 1663469617, 1613138993], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1562808369, 1478923317, 1428592693, 1395039285, 1327931449, 1294378041], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244047417, 1193716797, 1160163389, 1126609981, 1076279361, 1042725953], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1025949761, 975619141, 958842949, 925289541, 891736137, 858182729], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [841406537, 807853133, 791076941, 1100085387535, 1100102163731, 5455906069], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100118939927, 1100135716123, 9717317917, 1100135715107, 1100169268519, 9666985257], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169267503, 1100202820915, 13911619893, 1100202819899, 1100236373311, 13861287233], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100253149511, 925266253, 1100269925711, 1100286701911, 858156381, 1100320255327], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100337031527, 5086013805, 1100286698867, 1100253143419, 5018903933, 1100202810759], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [9246761357, 1100169255311, 1100118922651, 1099666219419, 1099666218403, 540185001], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099666217387, 1099666216371, 489852341, 1099666215355, 57792, 1099666214343], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57796, 16833992, 1099666213327, 16833996, 33610192, 33610196], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099666212315, 50386392, 50386396, 1099682988515, 67162592, 67162596], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [67162600, 1099682987503, 83938796, 83938800, 100714996, 1099682986491], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [100715000, 100715004, 117491200, 1099666208263, 117491204, 117491208], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [134267404, 1099615810067, 134267408, 134267412, 151043608, 151043612], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [1099548700195, 151043616, 167819812, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 138 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1293380645, 1226272809, 1159164969, 1108834345, 1041726509, 991395885], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [957842477, 1680246833, 1613138993, 1562808369, 1495700533, 1445369909], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395039285, 1327931449, 1277600825, 1244047417, 1193716797, 1160163389], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1109832765, 1076279361, 1042725953, 1009172545, 958841925, 942065733], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [908512325, 874958921, 841405513, 824629321, 791075917, 774299725], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100085387531, 1100102163727, 1100118939923, 5455906069, 1100135716119, 9717317917], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100135715103, 1100169268515, 9666985257, 1100169267499, 1100202820911, 13911619893], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100219597111, 1100219596095, 13861287233, 1100236372295, 1100286702923, 908489041], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100286701911, 858156381, 1100320255327, 1100337031527, 1100303476079, 1100253143419], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100202810759, 1100152478099, 1099649442199, 1100102145439, 1099649441183, 1099666217383], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [540185001, 1099666216367, 489852341, 1099666215351, 57784, 57788], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099666214339, 16833984, 16833988, 1099682990539, 16833992, 33610188], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [33610192, 1099682989527, 50386388, 50386392, 67162588, 1099666211299], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [67162592, 67162596, 1099649367531, 83938792, 83938796, 83938800], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099699763703, 100714996, 100715000, 100715004, 117491200, 1099666208263], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [117491204, 134267400, 1099548769807, 134267404, 1099615810067, 134267408], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [134267412, 151043608, 151043612, 1099548700195, 151043616, 167819812], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1125611561, 1058503725, 1008173101, 957842477, 1697024049, 1629916209], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1562808369, 1495700533, 1445369909, 1395039285, 1327931449, 1294378041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1244047417, 1193716797, 1143386173, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1009172545, 958841925, 925288517, 908512325, 858181705, 841405513], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [807852105, 774298701, 757522509, 1099631616263, 1100102163723, 1100118939919], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [5455906069, 1100118938903, 1100152492315, 9700540705, 1100152491299, 1100186044711], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099951169831, 9650208045, 1100186043695, 1100202819895, 13894842681, 1100236373307], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100253149507, 1100286702923, 1100303479123, 1100320255327, 1100337031527, 1100286698867], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100253143419, 1100202810759, 1100152478099, 1099649442195, 1099666218395, 1100102145439], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099666217379, 540185001, 1099666216363, 1099666215351, 57780, 473075129], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57784, 1099666214335, 57788, 16833984, 16833988, 1099666213323], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610184, 33610188, 1099682989523, 50386384, 50386388, 50386392], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099682988511, 67162588, 67162592, 83938788, 1099649367531, 83938792], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938796, 100714992, 1099699763703, 100714996, 100715000, 117491196], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [117491200, 1099666208263, 117491204, 134267400, 1099531992591, 134267404], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099615810067, 134267408, 151043604, 151043608, 151043612, 1099548700195], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [151043616, 167819812, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [974619693, 1697024049, 1629916209, 1579585585, 1512477749, 1445369909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1395039285, 1344708665, 1294378041, 1244047417, 1193716797, 1160163389], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1109832765, 1059502145, 1025948737, 992395329, 958841925, 925288517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [891735109, 858181705, 824628297, 807852105, 757521485, 740745293], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099631616259, 1099648392455, 1100118939919, 1100135716115, 5439128857, 1100135715099], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100169268511, 1099951169827, 1100169267495, 1099951168811, 1100186043695, 1100219597107], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100236373307, 1100253149507, 1100286702923, 1100286701911, 1100320255327, 1100337031527], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100286698867, 1100236366207, 1100202810759, 1099666219407, 1100152478099, 1099666218391], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100085368227, 1099649440163, 1099666216363, 523407789, 1099666215347, 57780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [473075129, 57784, 1099666214335, 16833980, 16833984, 1099682990535], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610180, 33610184, 33610188, 1099682989523, 50386384, 50386388], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162584, 1099682988511, 67162588, 67162592, 83938788, 1099649367531], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938792, 83938796, 100714992, 1099699763703, 100714996, 100715000], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [117491196, 117491200, 1099666208263, 117491204, 134267400, 1099531992591], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [134267404, 1099615810067, 134267408, 151043604, 151043608, 151043612], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099548700195, 151043616, 167819812, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1579585585, 1512477749, 1462147125, 1411816501, 1344708665, 1294378041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1260824633, 1193716797, 1160163389, 1109832765, 1059502145, 1025948737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [992395329, 942064709, 925288517, 891735109, 841404489, 824628297], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [791074889, 757521485, 723968077, 1099648393471, 1099631615239, 1100118939915], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100135716115, 1100152492311, 1100169268511, 1099951169827, 1100169267495, 1099967946023], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100202820907, 1100219597107, 1100236373307, 1100269926723, 1100286702923, 1100303479127], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100320255327, 1100320254315, 1100286698867, 1100236366207, 1100186033547, 1099649442191], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [540187029, 1099666218391, 1099666217375, 556963233, 1099666216363, 523407789], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099666215347, 57776, 57780, 57784, 1099666214335, 16833980], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16833984, 1099682990535, 33610180, 33610184, 33610188, 1099682989523], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386384, 50386388, 67162584, 1099682988511, 67162588, 67162592], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938788, 1099649367531, 83938792, 83938796, 100714992, 100714996], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099682986491, 100715000, 117491196, 117491200, 1099666208263, 117491204], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267400, 1099548769807, 134267404, 134267408, 1099599032855, 134267412], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [70621721, 151043608, 151043612, 1099548700195, 151043616, 167819812], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4298479145, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1411816501, 1344708665, 1311155257, 1260824633, 1193716797, 1160163389], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1126609981, 1076279361, 1025948737, 992395329, 958841925, 925288517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [891735109, 841404489, 824628297, 791074889, 757521485, 723968077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099631616255, 1099631615239, 1100118939915, 1100135716115, 1100152492311, 1100169268511], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099967947039, 1100186044711, 1099967946023, 1100186043695, 1100219597107, 1100253150523], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100253149511, 1100269925711, 1100303479127, 1100337032543, 1100320254315, 506635637], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [523411837, 540188041, 1099649442191, 1099649441175, 1099666217375, 1099666216363], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099666215347, 57776, 57780, 16833976, 1099666214335, 16833980], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16833984, 33610180, 1099666213323, 33610184, 33610188, 1099682989523], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50386384, 50386388, 67162584, 1099699765727, 67162588, 67162592], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [83938788, 83938792, 1099682987503, 83938796, 104179185, 100714992], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [100714996, 1099699763707, 100715000, 120955389, 117491196, 117491200], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099666208263, 117491204, 117491208, 120954381, 42508, 134267404], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [42512, 134267408, 42516, 1099599032855, 134267412, 42520], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043608, 16818716, 151043612, 16818720, 151043616, 16818724], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099531922983, 151043620, 16818728, 167819816], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group3
