import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass9

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 973148169, 2181436425, 10771830793, 2165122061, 2148345873], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2047683601, 1863135249, 1695364117, 1561147413, 1443707925, 1762738201], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1645298713, 1561413657, 1460751389, 1376866333, 1309758493, 1242650657], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1192320033, 1141989409, 1074881573, 1041328165, 1007774757, 957444137], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [923890729, 907114537, 2032696365, 2015920173, 1965589549, 1881704497], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1831373873, 1797820465, 1730712629, 1697159221, 1663605813, 1613275193], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1579721785, 1546168377, 1495837757, 1462284349, 1445508157, 1395177537], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1378401345, 1361625153, 1328071749, 1294518341, 1277742149, 1244188745], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1227412553, 1227413577, 1193860173, 1177083981, 14077137141, 2652420], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [5404914953, 5371359505, 9632771353, 9599215905, 13860627753, 13810295093], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13759962433, 18004597069, 17954264409, 22182121833, 1100220129643, 1100203351407], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26443529585, 1100186572147, 1100186573171, 1100169793911, 1100153015675, 1100136237439], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100102681991, 574275977, 26326088077, 557497741, 540588433, 3716504], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [4785222045, 4751666597, 30486836653, 4718111149, 8979522997, 8945902013], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [8912346565, 13173758413, 269562321, 13140202965, 17384837601, 17351282153], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [17300949493, 4379979261, 21528806917, 21478474257], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i3 : checks (tilesOf batches) 132 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 132 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 132 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10771830793, 2165122061, 2148345873, 2047683601, 1846358033, 1678586901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1527592981, 1410153493, 1729183769, 1611744281, 1527859225, 1410419741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1343311901, 1276204061, 1192319009, 1141988385, 1091657761, 1024549925], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [990996517, 957443109, 907112489, 873559081, 840005673, 2032696365], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1965588525, 1915257901, 1831372849, 1781042225, 1730711601, 1680380981], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1630050357, 1596496949, 1546166329, 1512612921, 1479059513, 1428728893], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1411952701, 1378399293, 1344845889, 1311292481, 1294516289, 1260962885], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1227409477, 1210633285, 1177079881, 1160303689, 1143527497, 1109974093], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1109975117, 1193834741, 1160279293, 5421691141, 5388135693, 9649547541], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [9615992093, 13860626729, 13810294069, 18054928705, 17987818833, 1100287237467], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100287238491, 1100270459231, 17920708961, 1100253680995, 1100236902759, 26477084009], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100220124523, 1100203346287, 1100169790839, 1100153012603, 1100136234367, 26359642501], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100102547847, 1100085769611, 540586385, 523808149, 4785219997, 4751664549], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [26208646569, 4718043565, 8979455413, 8945899965, 13190534601, 286339533], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13156979153, 13106646493, 17351281129, 17284171257, 4379979261, 21528805893], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i6 : checks (tilesOf batches) 132 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 132 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 132 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2165122061, 2148345873, 2064460817, 1863135249, 1678586901, 1544370197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1410153493, 1729183769, 1611744281, 1511082009, 1393642525, 1326534685], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1242649629, 1175541793, 1108433953, 1058103329, 990995493, 957442085], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [907111461, 856780841, 823227433, 806451241, 1999141933, 1932034093], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1864926253, 1797818417, 1747487793, 1697157169, 1630049333, 1596495925], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1546165301, 1495834681, 1462281273, 1428727865, 1378397245, 1344843837], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1328067645, 1277737025, 1260960833, 1227407425, 1193854021, 1177077829], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1160301637, 1126748233, 1109972041, 1093195849, 1059642445, 1042866253], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1227389165, 1210610929, 5472022777, 5438467329, 9683101965, 9649546517], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13894181153, 13843848493, 13776738621, 18021373257, 1100354347339, 1100337569103], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100320790867, 1100304012631, 1100287234395, 17937486173, 1100270456159, 1100253677923], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100236899687, 26477084009, 1100220121451, 1100186566003, 1100169656695, 1100136101247], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100119323011, 26342865289, 574139785, 540584337, 4801996185, 4768375201], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [26208646569, 4734819753, 8979454389, 8945898941, 13190533577, 269562321], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13140200917, 13089868257, 17334502893, 17267393021, 4363202049, 21495250445], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i9 : checks (tilesOf batches) 132 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 132 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 132 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1879912465, 1695364117, 1544370197, 1426930709, 1745960985, 1611744281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1511082009, 1393642525, 1309757469, 1242649629, 1158764577, 1091656737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1041326113, 974218277, 923887653, 890334245, 840003625, 806450217], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [772896809, 1982364717, 1915256877, 1848149037, 1764263985, 1713933361], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1663602737, 1596494901, 1562941493, 1512610869, 1462280249, 1428726841], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1395173433, 1344842813, 1311289405, 1277735997, 1244182593, 1210629185], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1193852993, 1143522373, 1126746181, 1109969989, 1076416585, 1042863177], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1026086985, 992533581, 992534605, 1260943589, 1227388141, 5488799989], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [5455244541, 9716656389, 9666323729, 9615991069, 13860625705, 13793515833], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100320660799, 1100287107391, 1100337436995, 1100354213191, 18021373257, 1100337566031], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100320787795, 1100304009559, 17954263385, 1100287231323, 1100253675875, 1100236897639], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26460306797, 1100203211119, 1100186432883, 1100152877435, 1100119321987, 26342865289], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [574138761, 540583313, 4801929625, 4768374177, 26191869357, 4718041517], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8979453365, 8929120705, 13173755341, 252785109, 13123422681, 17351280105], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17284170233, 1099616215547, 1099582660099, 17217060361, 1099549104651, 3921424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 132 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 132 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 132 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1443707925, 1762738201, 1628521497, 1527859225, 1410419741, 1326534685], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1242649629, 1158764577, 1091656737, 1041326113, 974218277, 923887653], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [873557029, 823226409, 789673001, 756119593, 1965587501, 1898479661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1831371821, 1764263985, 1697156145, 1646825521, 1579717685, 1529387061], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1495833653, 1428725817, 1395172409, 1361619001, 1311288381, 1277734973], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1244181565, 1193850945, 1177074753, 1143521345, 1109967941, 1093191749], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1059638341, 1026084937, 1009308745, 992532553, 958979149, 942202957], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1277720801, 1244165353, 5505577201, 5472021753, 9716656389, 9666323729], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9615991069, 13860625705, 1100287107379, 1100303883575, 13793515833, 1100320659771], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100337435967, 1100370989379, 1100370988359, 18021373257, 1100337563983, 1100320785747], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100304007511, 17937486173, 1100270452063, 1100253542755, 1100219987307, 26443529585], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100186431859, 1100152876411, 607693185, 574137737, 540516753, 4785151389], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4751595941, 8996230577, 8945897917, 13190532553, 13123422681, 13073090021], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099616215535, 17300947445, 1099616214519, 1099599436287, 17233837573, 1099565880839], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57864, 57868, 3920400, 16834064], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1544636441, 1427196957, 1343311901, 1259426845, 1158764577, 1108433953], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1041326113, 974218277, 923887653, 873557029, 806449193, 772895785], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [739342377, 1965587501, 1898479661, 1831371821, 1747486769, 1697156145], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1630048305, 1562940469, 1512609845, 1479056437, 1411948601, 1378395193], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1344841785, 1277733949, 1244180541, 1227404349, 1177073729, 1143520321], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1126744129, 1076413509, 1059637317, 1026083909, 992530505, 975754313], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [958978121, 908647501, 891871309, 1294498013, 1260942565, 5522354413], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [5472021753, 9716656389, 9666323729, 13910958365, 1100303884583, 1100320660779], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13843848493, 1100320659763, 1100354213175, 13793515833, 1100370989371, 1100387765567], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100370987335, 1100354340171, 18004596045, 1100320784723, 1100304006487, 1100270319967], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17920708961, 1100236764519, 1100219986283, 1100186430835, 22131789173, 624470397], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [590914949, 22031124877, 557293965, 4801928601, 4768373153, 9013007789], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8962675129, 13190532553, 13140199893, 13073090021, 1099616215527, 1099616214511], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [17300947445, 1099632990711, 1099582658051, 57856, 17233837573, 57860], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099549102603, 16834056, 16834060, 3919376, 16834064], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1259426845, 1175541793, 1108433953, 1041326113, 974218277, 923887653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [873557029, 823226409, 772895785, 739342377, 1965587501, 1898479661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1831371821, 1747486769, 1697156145, 1630048305, 1562940469, 1512609845], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1462279221, 1411948601, 1361617977, 1328064569, 1277733949, 1227403325], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1193849917, 1160296513, 1126743105, 1093189697, 1059636293, 1026082885], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1009306693, 958976073, 942199881, 925423689, 891870285, 858316877], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1294498013, 1260942565, 5505577201, 5472021753, 9716656389, 9666323729], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13910958365, 1100320661791, 1100320660775, 1100337436971, 13843848493, 1100354213167], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100370989363, 1100387765563, 13776738621, 1100404541759, 1100370986311, 1100354339147], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18004596045, 1100320783699, 1100287097179, 1100270318943, 1100236763495, 1100186430835], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100152875387, 607692161, 557293965, 4818705813, 4768373153, 9013007789], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8962675129, 8895565257, 13140199893, 1099616215523, 13073090021, 1099616214507], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099616213491, 17300947445, 1099616212475, 57852, 1099582657027, 57856], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [17233837573, 16834052, 16834056, 1099532324367, 33610252, 33610256], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1058103329, 990995493, 923887653, 890334245, 823226409, 772895785], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [739342377, 1982364717, 1915256877, 1831371821, 1747486769, 1697156145], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1630048305, 1562940469, 1512609845, 1462279221, 1395171385, 1361617977], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1311287353, 1260956733, 1227403325, 1193849917, 1143519297, 1109965889], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1076412481, 1026081861, 1009305669, 975752261, 942198857, 925422665], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [891869257, 858315853, 841539661, 1294498013, 1260942565, 5505577201], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [5455244541, 9716656389, 9649546517, 1100303884571, 1100320660767, 13894181153], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100354214179, 1100354213163, 1100370989359, 1100404542771, 1100421318971, 1100404540735], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100370985287, 1100337560911, 1100303874391, 1100270318943, 1100236763495, 1100203208047], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100169652599, 607692161, 574071177, 4818705813, 4768373153, 9013007789], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8962675129, 8895565257, 13140199893, 1099616215515, 1099632991715, 13073090021], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099616213487, 1099616212471, 57844, 17284170233, 57848, 1099599434239], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57852, 16834048, 16834052, 17217060361, 1099549101579, 33610248], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [33610252, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 132 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [890334245, 823226409, 789673001, 739342377, 1999141933, 1915256877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1848149037, 1764263985, 1697156145, 1646825521, 1562940469, 1512609845], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462279221, 1395171385, 1361617977, 1311287353, 1260956733, 1210626109], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1177072701, 1126742081, 1093188673, 1076412481, 1026081861, 992528453], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975752261, 925421641, 908645449, 875092041, 841538637, 824762445], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1294498013, 1244165353, 5505577201, 5455244541, 1100303884567, 1100320660763], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100354214175, 1100354213159, 1100387766571, 1100387765555, 1100421318967, 1100404540735], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100370985287, 1100354338123, 1100320651603, 1100287096155, 1100253540707, 1100203208047], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100169652599, 607692161, 574071177, 4818705813, 4768373153, 9013007789], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8945897917, 13190532553, 1099632992727, 13123422681, 1099632991711, 13056312809], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099616213483, 1099632989683, 57844, 17284170233, 57848, 1099599434239], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [16834044, 16834048, 1099565878791, 33610244, 33610248, 17200283149], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [33610252, 3918352, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [756119593, 2015919149, 1932034093, 1864926253, 1781041201, 1713933361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1646825521, 1579717685, 1529387061, 1462279221, 1411948601, 1361617977], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311287353, 1260956733, 1210626109, 1177072701, 1126742081, 1093188673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059635265, 1009304645, 992528453, 958975045, 908644425, 891868233], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [858314825, 824761421, 807985229, 1277720801, 1100320661779, 1100337437975], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100354214171, 1100370990371, 1100387766567, 1100404542767, 1100421318967, 1100421317947], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100387762499, 1100354338123, 1100320651603, 1100287096155, 1100253540707, 1100203208047], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [658024821, 607692161, 557293965, 4818705813, 4751595941, 8996230577], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8945897917, 13173755341, 1099616215511, 13106645469, 1099616214495, 1099632990695], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17334502893, 1099616212467, 57840, 57844, 1099616211451, 16834040], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17267393021, 16834044, 16834048, 1099565878791, 33610244, 33610248], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386444, 17183505937, 3918352, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1864926253, 1781041201, 1713933361, 1663602737, 1579717685, 1529387061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1479056437, 1411948601, 1361617977, 1311287353, 1260956733, 1227403325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1177072701, 1126742081, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [958975045, 908644425, 875091017, 858314825, 807984205, 791208013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100320661775, 1100337437971, 1100354214171, 1100370990367, 1100387766567, 1100404542767], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438096179, 1100421317947, 1100387762499, 1100354338123, 1100320651603, 1100287096155], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100236763495, 1100203208047, 658024821, 607692161, 557293965, 4801928601], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4751595941, 8996230577, 8929120705, 13173755341, 1099616215507, 1099632991707], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13106645469, 1099616213479, 17334502893, 1099632989679, 57836, 57840], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57844, 1099616211451, 16834040, 16834044, 33610240, 1099565878791], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610244, 33610248, 50386444, 3918352, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1663602737, 1596494901, 1546164277, 1479056437, 1411948601, 1378395193], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1328064569, 1260956733, 1227403325, 1177072701, 1126742081, 1093188673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059635265, 1009304645, 975751237, 942197829, 908644425, 875091017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [858314825, 807984205, 791208013, 1100320661775, 1100337437971, 1100354214171], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100370990367, 1100387766567, 1100421319979, 1100438096179, 1100421317947, 1100387762499], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100354338123, 1100320651603, 1100287096155, 1100236763495, 1100203208047, 641247609], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [590914949, 557293965, 4801928601, 4734818729, 8979453365, 8929120705], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099616215507, 1099632991707, 1099616213479, 1099632989679, 57836, 57840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57844, 1099616211451, 16834040, 16834044, 33610240, 1099565878791], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [33610244, 33610248, 50386444, 3918352, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1495833653, 1428725817, 1378395193, 1328064569, 1277733949, 1227403325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1193849917, 1126742081, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [942197829, 908644425, 875091017, 841537609, 807984205, 774430797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100337438987, 1100337437971, 1100370991383, 1100370990367, 1100387766567, 1100421319979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100438096179, 1100421317947, 1100387762499, 1100354338123, 1100320651603, 1100270318943], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100236763495, 1100186430835, 641247609, 590914949, 540516753, 4785151389], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099616215507, 1099632991707, 1099616213479, 1099632989679, 57836, 57840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57844, 1099616211451, 16834040, 16834044, 33610240, 1099565878791], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33610244, 33610248, 50386444, 3918352, 50386448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group9
