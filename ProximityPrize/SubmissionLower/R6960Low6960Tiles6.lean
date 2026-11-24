import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass6

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2248215557, 973148169, 1107432457, 6526998537, 2215256077, 2013930509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1762273297, 1577724945, 1426731025, 1292514325, 1191852053, 1107966997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1007304729, 956974105, 889866265, 839535645, 789205021, 23625290781], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [15001807909, 10673290285, 2066581553, 2066582577, 2033029169, 1965921333], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1915590709, 1865260085, 1814929465, 1781376057, 1747822649, 1697492029], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1663938621, 1630385213, 1580054593, 1563278401, 1529724993, 1496171589], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1462618181, 1445841989, 1412288585, 1395512393, 1378736201, 1345182797], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1328406605, 14229524701, 18474159337, 18440603889, 9832173813, 18373494017], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22618128653, 22534241569, 31040747829, 30940083533, 35117609321, 34966613389], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100119138703, 1100102360467, 1100085713303, 1100068935067, 1100052222367, 1100035444131], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100018665895, 1099985110447, 1099968332211, 34782063033, 1099934711227, 1099917932991], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099884377543, 339194317, 305638869, 4567050717, 4533495269, 4499939821], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [34547181041, 8761351669, 8710887937, 8660555277, 8610222617], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i3 : checks (tilesOf batches) 135 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 135 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 135 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6526998537, 2215256077, 2013930509, 1762273297, 1577724945, 1409953809], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1275737109, 1158297621, 1074412565, 973750297, 906642457, 856311833], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [789203997, 738873373, 23625290781, 15001807909, 6378322989, 2083357741], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2066581553, 2033028145, 1982697521, 1915589685, 1865259061, 1814928437], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1764597817, 1714267193, 1680713785, 1630383165, 1596829757, 1563276349], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1512945729, 1496169537, 1462616129, 1429062725, 1395509317, 1378733125], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1345179721, 1328403529, 1311627337, 1278073933, 1261297741, 14279856337], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18524490973, 18474158313, 18423825653, 22651683077, 22567795993, 31074302253], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [30956860745, 30839419237, 1100018475391, 1100035251587, 1100035250567, 1100052026763], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [34966613389, 1100068802959, 1100085579155, 1100085709207, 1100052219295, 1100035441059], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100001820075, 1099985041839, 1099951486391, 34782063033, 1099917930943, 372747717], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [339192269, 305636821, 4550271457, 4516716009, 34547181041, 4466252277], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099616018939, 4415919617, 1099599240707, 1099616016903, 8660554253, 1099582461455], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099548906007, 1099532198423, 8610221593, 56856, 3722780, 16834076], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i6 : checks (tilesOf batches) 135 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 135 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 135 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2047484941, 1779050513, 1577724945, 1426731025, 1275737109, 1158297621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1074412565, 973750297, 906642457, 839534617, 772426781, 722096157], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23625290781, 15001807909, 6378322989, 2083357741, 2049804337, 1999473713], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1932365873, 1865258037, 1814927413, 1764596789, 1714266169, 1663935545], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1630382137, 1580051517, 1546498109, 1512944701, 1462614081, 1445837889], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1412284481, 1361953861, 1345177669, 1328401477, 1278070857, 1261294665], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1244518473, 1210965069, 1194188877, 14296633549, 14246300889, 18490935525], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18423825653, 22651683077, 22567795993, 31074302253, 30956860745, 30822642025], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100018475375, 1100035251571, 1100035250551, 1100052026747, 1100068802943, 1100068801927], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100085578123, 34966613389, 1100119131535, 1100085707159, 1100052151711, 1100035373475], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100001818027, 1099968262579, 1099934707131, 34765285821, 389523905, 355968457], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [305635797, 4567047645, 4516583913, 1099616018923, 1099616017907, 4466251253], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099616016887, 34513626617, 1099616015871, 8710885889, 1099616014855, 57860], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57864, 1099582459407, 16834060, 8643776017, 33610256, 1099548903959], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [33610260, 50386456, 8593443357, 50386460], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i9 : checks (tilesOf batches) 135 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 135 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 135 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1443508241, 1292514325, 1175074837, 1074412565, 973750297, 906642457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [839534617, 755649565, 705318941, 23625290781, 15001807909, 6378322989], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2083357741, 2033027121, 1965919281, 1915588657, 1831703605, 1781372981], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1731042357, 1680711737, 1630381113, 1596827705, 1546497085, 1512943677], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1479390269, 1429059649, 1395506241, 1361952833, 1328399429, 1294846021], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1278069829, 1227739209, 1210963017, 1194186825, 1160633421, 1143857229], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [14313410761, 14263078101, 18490935525, 18423825653, 22651683077, 22567795993], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [31057525041, 30940083533, 1100018475363, 1100035251559, 1100035250539, 30805864813], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100052026735, 1100068802931, 1100068801915, 1100085578111, 1100102354311, 1100119130507], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100102352275, 1100068927899, 1100035372451, 1100001817003, 1099968261555, 1099934706107], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [389522881, 339190221, 4600602069, 1099616018911, 255171041, 1099599240679], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099616016875, 4499805677, 1099616015859, 1099632792059, 57848, 4432695805], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [16834044, 1099632791043, 16834048, 33610244, 8677330441, 1099599235595], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [33610248, 50386444, 50386448, 1099548902935, 50386452, 8610220569], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [67162648, 3719708, 67162652], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 135 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 135 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 135 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1091189781, 990527513, 906642457, 839534617, 772426781, 705318941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23625290781, 15001807909, 6378322989, 2083357741, 2016249905, 1949142065], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1898811441, 1814926389, 1764595765, 1714265141, 1647157305, 1613603897], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1563273273, 1512942653, 1479389245, 1445835837, 1395505217, 1361951809], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1328398401, 1278067781, 1261291589, 1227738181, 1194184777, 1177408585], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1143855177, 1110301773, 1093525581, 14313410761, 14246300889, 18490935525], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18423825653, 22634905865, 22551018781, 1100018475351, 1100035251547, 1100052027743], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100052026727, 1100068802923, 1100085579119, 1100085578103, 1100119131515, 1100119130499], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100135906699, 1100102351251, 1100068926875, 1100035371427, 1100001815979, 1099968260531], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099917927871, 372744645, 322411985, 1099616018899, 1099616017883, 271948253], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099616016867, 4516582889, 1099616015851, 57836, 1099616014835, 57840], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [16834036, 4449473017, 1099616013819, 16834040, 33610236, 1099632790019], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [33610240, 8694107653, 50386436, 50386440, 1099582457359, 67162636], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [67162640, 8626997781, 1099548901911, 83938836, 83938840, 83938844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [856311833, 772426781, 722096157, 23625290781, 15001807909, 6378322989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2083357741, 2016249905, 1949142065, 1882034225, 1814926389, 1747818549], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1697487925, 1630380089, 1596826681, 1546496057, 1496165437, 1445834813], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1412281405, 1361950785, 1328397377, 1294843969, 1261290565, 1227737157], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1194183749, 1160630345, 1143854153, 1110300745, 1076747341, 1059971149], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [14296633549, 18541268185, 18474158313, 1100018475343, 1100035251539, 1100035250519], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100052026719, 1100068802915, 1100085579111, 1100085578095, 1100102354295, 1100119130491], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100135906691, 1100135905675, 1100102350227, 1100068925851, 1100018593191, 1099985037743], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099934705083, 389521857, 1099616018891, 339189197, 1099616017875, 1099632794071], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [288725465, 1099616015843, 57828, 4516582889, 1099616014827, 57832], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16834028, 1099616013811, 16834032, 4466250229, 33610228, 1099632790011], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610232, 50386428, 50386432, 4399140357, 1099616011783, 67162628], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162632, 1099582456335, 83938828, 83938832, 8626997781, 83938836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099532123675, 100715032, 100715036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [23625290781, 15001807909, 6378322989, 2083357741, 2016249905, 1949142065], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1882034225, 1798149173, 1747818549, 1697487925, 1630380089, 1580049465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1529718841, 1479388221, 1429057597, 1395504189, 1345173569, 1311620161], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1278066753, 1227736133, 1210959941, 1177406533, 1127075913, 1110299721], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1093523529, 1043192909, 1026416717, 1100018475335, 1100035251531, 1100035250515], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100052026711, 1100068802907, 1100068801891, 1100085578091, 1100102354287, 1100119130487], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100135906687, 1100152682887, 1100119127439, 1100085703063, 1100035370403, 1100001814955], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099951482295, 389521857, 1099616018883, 1099616017867, 339189197, 1099616016851], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [288725465, 1099616015835, 57820, 1099632792035, 57824, 4533360101], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16834020, 1099632791019, 16834024, 33610220, 33610224, 4466250229], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632790007, 50386420, 50386424, 1099632788991, 50386428, 67162624], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4399140357, 67162628, 1099599233547, 83938824, 83938828, 83938832], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8626997781, 1099548900887, 100715028, 100715032, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [19313549345, 10690065449, 2083356717, 2083357741, 2016249905, 1949142065], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1882034225, 1798149173, 1747818549, 1697487925, 1630380089, 1580049465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1529718841, 1462611005, 1429057597, 1395504189, 1328396353, 1294842945], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1261289537, 1210958917, 1194182725, 1160629317, 1110298697, 1093522505], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059969097, 1026415693, 992862285, 1100018475327, 1100018474311, 1100035250507], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100052026707, 1100068802903, 1100068801887, 1100085578087, 1100102354283, 1100119130483], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100135906683, 1100152682883, 1100119127439, 1100085703063, 1100052147615, 1100001814955], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099951482295, 1099616018875, 389521857, 1099616017859, 1099632794059, 339189197], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099616015831, 57812, 288725465, 57816, 1099616014815, 16834012], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16834016, 4533360101, 1099632791015, 16834020, 33610216, 33610220], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632790003, 50386416, 4466250229, 50386420, 1099632788987, 67162616], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162620, 67162624, 8694107653, 1099616010759, 83938820, 83938824], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938828, 1099565678099, 100715024, 8626997781, 100715028, 117491224], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [3717660, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 135 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [15001807909, 6378322989, 2083357741, 2033027121, 1965919281, 1898811441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1814926389, 1747818549, 1697487925, 1630380089, 1580049465, 1529718841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462611005, 1429057597, 1378726973, 1328396353, 1294842945, 1261289537], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1210958917, 1177405509, 1143852101, 1093521481, 1076745289, 1043191881], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009638477, 976085069, 1100018475323, 1100018474307, 1100035250503, 1100052026703], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100068802899, 1100068801883, 1100085578083, 1100102354283, 1100119130483, 1100135906683], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100152682883, 1100135904651, 1100085703063, 1100052147615, 1100001814955, 1099951482295], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099616018871, 1099616017855, 389521857, 1099632794055, 339189197, 1099616015827], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57808, 57812, 288725465, 1099632792027, 16834008, 16834012], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632791011, 16834016, 33610212, 4516582889, 33610216, 1099632789999], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386412, 50386416, 50386420, 4449473017, 1099632788987, 67162616], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162620, 83938816, 1099616010759, 83938820, 8677330441, 83938824], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [100715020, 1099565678099, 100715024, 100715028, 8610220569, 117491224], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [3717660, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [6395099177, 2083356717, 2083357741, 2049804337, 1965919281, 1898811441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1814926389, 1764595765, 1697487925, 1630380089, 1580049465, 1529718841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462611005, 1429057597, 1378726973, 1328396353, 1278065729, 1244512321], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1194181701, 1160628293, 1127074885, 1093521481, 1059968073, 1026414665], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [992861261, 959307853, 1100018475319, 1100018474303, 1100052027715, 1100052026699], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100052025683, 1100085579095, 1100102355295, 1100102354279, 1100119130479, 1100152683895], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100152682883, 1100135904651, 1100085703063, 1100052147615, 1100001814955, 1099616018867], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099951482295, 1099632795067, 389521857, 1099616016839, 339189197, 1099616015823], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57804, 57808, 1099632792023, 57812, 16834008, 271948253], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16834012, 1099632791011, 33610208, 33610212, 4516582889, 50386408], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632789999, 50386412, 50386416, 1099649566199, 67162612, 4449473017], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162616, 67162620, 1099632787971, 83938816, 83938820, 8677330441], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938824, 100715020, 1099565678099, 100715024, 100715028, 117491224], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8593443357, 3717660, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [2083357741, 2049804337, 1982696497, 1915588657, 1831703605, 1764595765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1714265141, 1647157305, 1580049465, 1529718841, 1479388221, 1429057597], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1378726973, 1328396353, 1278065729, 1244512321, 1194181701, 1160628293], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1127074885, 1076744265, 1059968073, 1026414665, 976084045, 959307853], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100018475319, 1100035251515, 1100035250499, 1100052026699, 1100068802895, 1100085579095], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100085578079, 1100102354279, 1100119130479, 1100152683895, 1100152682883, 1100135904651], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100085703063, 1100035370403, 1100001814955, 1099616018867, 1099951482295, 1099616017851], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099632794051, 372744645, 1099616015823, 57804, 322411985, 57808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632792023, 16834004, 16834008, 271948253, 16834012, 1099632791011], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [33610208, 33610212, 1099649567211, 50386408, 4499805677, 50386412], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386416, 1099649566199, 67162612, 67162616, 4432695805, 67162620], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632787971, 83938816, 83938820, 83938824, 8660553229, 100715020], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099565678099, 100715024, 100715028, 117491224, 8593443357, 3717660], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1932365873, 1848480821, 1781372981, 1714265141, 1647157305, 1596826681], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1546496057, 1479388221, 1429057597, 1378726973, 1328396353, 1294842945], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1244512321, 1194181701, 1160628293, 1127074885, 1076744265, 1043190857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1026414665, 976084045, 942530637, 1100018475315, 1100035251515, 1100035250499], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100052026695, 1100068802895, 1100085579095, 1100085578079, 1100102354279, 1100135907695], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100135906683, 1100152682883, 1100135904651, 1100085703063, 1100035370403, 1099985037743], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099616018863, 1099934705083, 1099616017851, 1099616016835, 372744645, 1099632793035], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57800, 57804, 4617379281, 57808, 1099632792023, 16834004], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16834008, 33610204, 255171041, 1099632791011, 33610208, 33610212], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099649567211, 50386408, 50386412, 4483028465, 50386416, 1099649566199], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162612, 67162616, 67162620, 4415918593, 83938816, 1099616010759], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938820, 83938824, 100715020, 1099565678099, 100715024, 100715028], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [117491224, 3717660, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1731042357, 1663934521, 1596826681, 1546496057, 1479388221, 1429057597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1395504189, 1328396353, 1294842945, 1244512321, 1194181701, 1160628293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1127074885, 1076744265, 1043190857, 1009637449, 976084045, 942530637], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018475315, 1100018474299, 1100052027711, 1100052026695, 1100068802895, 1100085579095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100102355295, 1100119131495, 1100135907695, 1100135906683, 1100169460099, 1100119127439], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100085703063, 1100035370403, 1099985037743, 1099616018863, 1099632795063, 423077305], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099616016835, 355967433, 1099632793035, 57800, 57804, 57808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4600602069, 1099632792023, 16834004, 16834008, 33610204, 1099632791011], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33610208, 33610212, 50386408, 1099632789999, 50386412, 50386416], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [67162612, 1099632788987, 67162616, 67162620, 83938816, 1099616010759], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [83938820, 83938824, 100715020, 1099565678099, 100715024, 100715028], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [117491224, 117491228], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group6
