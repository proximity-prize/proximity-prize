import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass13

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 989925385, 6577198089, 10855914509, 6544173073, 2249207825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2114991125, 1963997205, 1813003285, 1678786585, 1578124313, 1477462041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1393576989, 1309691933, 1259361309, 1175476257, 1125145633, 1091592225], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1024484389, 990930981, 957377573, 2150068265, 2150069289, 2133293097], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2049408045, 1999077421, 1931969581, 1864861745, 1814531121, 1780977713], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1713869877, 1680316469, 1646763061, 1596432441, 1562879033, 1529325625], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1478995005, 1462218813, 1428665405, 1395112001, 1361558593, 1344782401], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1311228997, 1294452805, 1277676613, 1244123209, 1227347017, 1210570825], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1177017421, 14160957689, 9783831821, 9750276373, 9716720925, 13961355561], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13927800113, 18172434749, 18105324877, 18054992217, 1100320726379, 22266072429], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100303948143, 1100287169907, 1100270457207, 1100253678971, 22198962557, 1100236900735], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100220122499, 1100203344263, 1100186566027, 1100152945043, 22098298261, 624539029], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [3781020, 4869172641, 4835617193, 26292601261, 9097029041, 9063473593], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [9029787073, 26175159753, 8996231625, 8962676177, 13207310813, 13173755365], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [26024163821, 17418390001, 17368057341, 17300947469, 30168135185, 21545582105], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [21478472233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
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
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10872690697, 6560949261, 2249206801, 2249207825, 2114991125, 1947219989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1796226069, 1645232153, 1544569881, 1443907609, 1343245341, 1276137501], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1209029661, 1141921825, 1074813985, 1041260577, 974152741, 940599333], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [907045925, 2150068265, 2150069289, 2082961449, 1999076397, 1948745773], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1881637933, 1814530097, 1764199473, 1713868849, 1663538229, 1613207605], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1579654197, 1529323577, 1495770169, 1462216761, 1411886141, 1395109949], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1361556541, 1328003137, 1294449729, 1277673537, 1244120133, 1227343941], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1210567749, 1160237129, 1160238153, 1143461961, 1109908557, 5539196161], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9800608009, 9767052561, 14011687197, 13978131749, 13911021877, 18155656513], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18088546641, 1100387835227, 1100371056991, 22316404065, 1100354277731, 1100354278755], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100320722283, 1100303944047, 1100287165811, 22232516981, 1100270453111, 1100253674875], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100220053891, 1100203275655, 22131852685, 658092429, 641314193, 607758745], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4869170593, 26326155685, 4835615145, 4801928625, 4768373177, 26191936965], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [9013007813, 8979452365, 13224087001, 13173754341, 26040941033, 17418388977], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17351279105, 17300946445, 25873167889, 21528803869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [6560949261, 2249206801, 2249207825, 2131768341, 1947219989, 1796226069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1645232153, 1527792665, 1443907609, 1326468125, 1259360285, 1192252445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1108367393, 1058036769, 1007706145, 940598309, 907044901, 873491493], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2150068265, 2133292073, 2066184233, 1982299181, 1915191341, 1848083501], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1780975665, 1730645041, 1680314417, 1613206581, 1579653173, 1529322549], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1478991929, 1445438521, 1411885113, 1361554493, 1344778301, 1311224893], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1260894273, 1244118081, 1227341889, 1177011269, 1160235077, 1143458885], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1109905481, 1093129289, 1076353097, 1042799693, 5572750585, 9834162433], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9800606985, 9750274325, 13994908961, 13944576301, 18172433725, 1100354149707], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18105323853, 1100438165839, 1100421387603, 1100404609367, 1100387831131, 18038213981], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100371052895, 1100354274659, 1100320719211, 1100303940975, 1100287162739, 22232516981], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100253607291, 1100220051843, 691645829, 22148629897, 658090381, 624534933], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4885946781, 26326155685, 4852260261, 4801927601, 9063339449, 26191936965], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [9013006789, 8962674129, 13207308765, 26040941033, 13156976105, 17384833529], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17317723657, 25856390677, 1099599437335, 21545581081, 2717224], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [2249207825, 2148545557, 1963997205, 1813003285, 1662009369, 1544569881], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1443907609, 1326468125, 1259360285, 1175475229, 1091590177, 1041259553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [990928929, 923821093, 873490469, 839937061, 2150068265, 2116514857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2049407017, 1948744749, 1881636909, 1831306285, 1747421233, 1697090609], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1646759985, 1579652149, 1546098741, 1495768117, 1445437497, 1411884089], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1378330681, 1328000061, 1294446653, 1260893245, 1227339841, 1193786433], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1177010241, 1126679621, 1109903429, 1093127237, 1059573833, 1042797641], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1026021449, 992468045, 5606305009, 9867716857, 9817384197, 9767051537], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14011686173, 13961353513, 18189210937, 1100337372479, 1100354148675, 1100370924871], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100387701067, 18105323853, 1100438162767, 1100421384531, 1100404606295, 18038213981], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100371050847, 1100354272611, 1100320717163, 1100303938927, 22232516981, 1100270383479], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100236828031, 691644805, 22131852685, 658089357, 4919501205, 590847389], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [26309378473, 4835482025, 4801926577, 9046561213, 26175159753, 8996228553], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13240863189, 13173753317, 26024163821, 13123420657, 17351278081, 1099666546183], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099632990735, 17267390997, 1099599369751, 25839613465, 1099565814303, 19494437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1829780501, 1678786585, 1561347097, 1443907609, 1343245341, 1259360285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1175475229, 1091590177, 1041259553, 974151713, 923821093, 873490469], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [823159845, 2150068265, 2116514857, 2032629801, 1948744749, 1881636909], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1814529069, 1730644017, 1680313393, 1629982769, 1562874933, 1512544309], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1478990901, 1411883065, 1378329657, 1344776249, 1294445629, 1260892221], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1227338813, 1193785409, 1160232001, 1143455809, 1093125189, 1076348997], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1042795589, 1009242185, 992465993, 975689801, 942136397, 5623082221], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [5572749561, 9817384197, 9783828749, 14011686173, 13961353513, 1100337372467], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100354148663, 18189210937, 1100370924859, 1100404478271, 1100421254467, 1100438030667], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18105323853, 1100438160719, 1100404605271, 1100387827035, 18021436769, 1100354271587], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100337493351, 1100303937903, 22232516981, 1100270382455, 1100236827007, 691643781], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [658088333, 22115075473, 607624601, 4869036449, 26292601261, 4818703789], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [9063338425, 9013005765, 26158382541, 8962673105, 13190530529, 13123420657], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099666546171, 17351278081, 1099666545155, 1099632924171, 17284168209, 1099599368727], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099565813279, 56864, 19494437, 56868, 3852840, 3921448], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [16833064], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
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
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1460684825, 1360022557, 1276137501, 1192252445, 1108367393, 1041259553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [990928929, 923821093, 873490469, 823159845, 2150068265, 2116514857], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2032629801, 1948744749, 1881636909, 1814529069, 1730644017, 1680313393], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1613205553, 1546097717, 1495767093, 1462213685, 1395105849, 1361552441], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1327999033, 1277668413, 1244115005, 1210561597, 1160230977, 1126677569], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1109901377, 1059570757, 1042794565, 1009241157, 975687753, 958911561], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [942135369, 908581965, 5623082221, 9867716857, 9817384197, 9767051537], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14011686173, 1100337372459, 13944576301, 1100354148655, 1100370924851, 1100387701047], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100421254459, 18172433725, 1100421253443, 1100454806855, 1100438159695, 18088546641], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100421381459, 1100387826011, 1100354270563, 22299626853, 1100320715115, 1100287159667], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [22215739769, 1100253604219, 708420993, 674865545, 624401813, 4885813661], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4835481001, 9080115637, 9013005765, 8962673105, 13190530529, 13123420657], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099666546163, 1099616147963, 17351278081, 1099632924163, 1099632923147, 17284168209], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099599367703, 1099549104663, 56856, 1099565812255, 56860, 1099549103651], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [16833056, 19494437, 16833060, 3851816, 53800, 16833064], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1209029661, 1108367393, 1058036769, 990928929, 923821093, 873490469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [823159845, 2150068265, 2133292073, 2049407017, 1948744749, 1881636909], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1814529069, 1730644017, 1663536177, 1613205553, 1546097717, 1495767093], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1445436469, 1395105849, 1344775225, 1311221817, 1260891197, 1227337789], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1193784381, 1143453761, 1109900353, 1076346945, 1042793541, 1009240133], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [992463941, 958910537, 925357129, 908580937, 875027533, 5623082221], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9867716857, 9817384197, 14062018833, 13994908961, 1100337372451, 1100354148647], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100370924843, 13944576301, 1100387701043, 1100404477239, 1100438030651, 18155656513], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100454806851, 1100471583047, 1100438158671, 1100404603223, 1100371047775, 1100337492327], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100303936879, 1100270381431, 725198205, 674865545, 641179025, 4885813661], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4835481001, 4785148341, 9029782977, 8962673105, 13190530529, 1099666546155], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13123420657, 1099632925171, 1099632924155, 17351278081, 1099632923143, 1099632922127], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532327443, 56848, 17267390997, 56852, 1099582589467, 33609240], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099532326431, 16833052, 16833056, 1099532256807, 50385444, 2717224], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [50385448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1007706145, 923821093, 873490469, 839937061, 2150068265, 2150069289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2066184233, 1965521965, 1881636909, 1814529069, 1730644017, 1680313393], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1613205553, 1546097717, 1495767093, 1445436469, 1378328633, 1344775225], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1294444601, 1244113981, 1210560573, 1177007165, 1126676545, 1093123137], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059569729, 1026016325, 992462917, 975686725, 925356105, 908579913], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [891803721, 841473101, 5606305009, 9867716857, 9817384197, 14045241621], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099766029595, 1100337371427, 1100370924839, 1100387701035, 1100404477235, 1100438030647], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100454806847, 1100488360259, 1100454804811, 1100421380435, 1100387824987, 1100152954203], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100354269539, 1100320714091, 1100287158643, 725198205, 691642757, 641179025], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4885813661, 4835481001, 9080115637, 9013005765, 8962673105, 13190530529], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632925163, 13123420657, 1099632924151, 1099582660087, 1099632923135, 17334500869], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632922123, 1099549104651, 56840, 56844, 56848, 1099599366679], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [33609236, 17250613785, 33609240, 50385436, 1099549034019, 50385440], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [50385444, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [839937061, 2150068265, 2150069289, 2066184233, 1982299181, 1898414125], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831306285, 1747421233, 1680313393, 1629982769, 1546097717, 1495767093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1445436469, 1378328633, 1344775225, 1294444601, 1244113981, 1210560573], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160229949, 1109899329, 1076345921, 1059569729, 1009239109, 975685701], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [958909509, 908578889, 891802697, 858249289, 824695885, 5606305009], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099749252375, 1099766028571, 1100370924835, 1100387701031, 1100404477231, 1100438030643], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100454806843, 1100471583043, 1100471582023, 1100438157647, 1100169731411, 1100404602199], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169730395, 1100354269539, 1100320714091, 1100287158643, 725198205, 691642757], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [641179025, 4885813661, 4835481001, 9063338425, 9013005765, 13240863189], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13173753317, 1099632924147, 1099582660083, 13106643445, 1099649700347, 1099549039099], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632922119, 1099549104647, 56836, 17317723657, 56840, 56844], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099616143891, 33609232, 33609236, 17250613785, 33609240, 1099565811231], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50385436, 50385440, 67161636, 3850792, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2082961449, 1982299181, 1915191341, 1848083501, 1747421233, 1697090609], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1629982769, 1562874933, 1495767093, 1445436469, 1395105849, 1344775225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1294444601, 1244113981, 1193783357, 1160229949, 1109899329, 1076345921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1042792513, 992461893, 975685701, 942132293, 908578889, 875025481], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [858249289, 807918669, 1099749252371, 1099749251355, 1099766027551, 1100387701031], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100421254443, 1100438030643, 1100471584055, 1100488360255, 1100471582023, 1100438157647], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100169731407, 1100404602199, 1100186507607, 1100371046751, 1100186506591, 1100320714091], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100287158643, 725198205, 674865545, 641179025, 4885813661, 4818703789], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9063338425, 8996228553, 13240863189, 13156976105, 1099582660079, 17384833529], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632923131, 1099532261883, 1099549038083, 1099549104643, 56832, 1099632922119], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56836, 17317723657, 56840, 33609228, 1099616143891, 33609232], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33609236, 50385432, 17233836573, 1099565811231, 50385436, 50385440], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67161636, 3850792, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1848083501, 1764198449, 1697090609, 1646759985, 1562874933, 1512544309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1462213685, 1395105849, 1344775225, 1294444601, 1244113981, 1210560573], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1160229949, 1109899329, 1076345921, 1042792513, 992461893, 958908485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [942132293, 891801673, 875025481, 841472073, 807918669, 1099749252371], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099749251351, 1099749250335, 1100387701027, 1100404477227, 1100438030639, 1100471584055], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488360255, 1100471582023, 1100438157647, 1100152954191, 1100186507603, 1100404602199], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100203283803, 1100354269539, 1100320714091, 1100287158643, 725198205, 674865545], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624401813, 4869036449, 4818703789, 9046561213, 8996228553, 13224085977], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13156976105, 1099599437291, 1099649700343, 1099549039095, 1099649699331, 1099549038083], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532327427, 56832, 56836, 16833032, 1099632921103, 33609228], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33609232, 33609236, 50385432, 1099565811231, 50385436, 50385440], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67161636, 3850792, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1646759985, 1579652149, 1512544309, 1462213685, 1395105849, 1361552441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1311221817, 1244113981, 1210560573, 1160229949, 1109899329, 1076345921], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1042792513, 992461893, 958908485, 942132293, 891801673, 858248265], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [841472073, 791141453, 1099749252367, 1099749251351, 1099766027547, 1100387701027], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100404477227, 1100438030639, 1100471584055, 1100488360255, 1100471582023, 1100085714251], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438157647, 1100186507603, 1100404602199, 1100203283803, 1100354269539, 1100320714091], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100270381431, 708420993, 674865545, 624401813, 4869036449, 4801926577], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9046561213, 1099632926167, 1099649700343, 1099549039095, 1099532328439, 56828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099649699331, 1099532260867, 1099532327427, 56832, 56836, 33609224], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632921103, 33609228, 33609232, 33609236, 50385432, 1099565811231], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50385436, 50385440, 67161636, 3850792, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1478990901, 1411883065, 1361552441, 1311221817, 1260891197, 1210560573], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1177007165, 1126676545, 1076345921, 1042792513, 992461893, 958908485], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [942132293, 891801673, 858248265, 841472073, 791141453, 1099749252367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099749251351, 1099766027547, 1100387701027, 1100404477227, 1100454807855, 1100471584055], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100488360255, 1100471582023, 1100085714251, 1100421380435, 1100186507603, 1100387824987], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100203283803, 1100354269539, 1100303936879, 758753653, 708420993, 4953055629], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [607624601, 1099632926167, 1099649700343, 1099532261879, 1099532328439, 16833020], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099649699331, 1099532260867, 1099532327427, 56832, 56836, 33609224], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33609228, 1099616143891, 33609232, 33609236, 50385432, 1099565811231], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50385436, 50385440, 67161636, 3850792, 67161640], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group13
