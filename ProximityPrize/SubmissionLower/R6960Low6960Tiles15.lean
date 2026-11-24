import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass15

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 989925385, 10838807561, 2232098829, 2232099853, 1963665425], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1745562641, 1594568721, 1443574805, 1326135317, 1225473045, 1124810777], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1057702937, 1007372313, 23641869341, 15018386469, 6411678761, 2099936301], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2099937325, 2083161133, 1999276081, 1948945457, 1898614833, 1848284213], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1797953589, 1764400181, 1714069561, 1663738937, 1630185529, 1596632125], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1563078717, 1529525309, 1495971905, 1462418497, 1445642305, 1395311685], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1378535493, 1361759301, 1328205897, 1311429705, 1294653513, 1261100109], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14127468793, 26930202893, 26879870233, 26812760361, 26728873277, 30923176277], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [30805734769, 1100203285887, 1100186507651, 1100169729415, 1100152951179, 1100136172943], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [605106577, 1100119394707, 1100102616471, 1100069061023, 1100052282787, 507099561], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [490321325, 4749077941, 456765877, 4718177725, 4701399489, 8962811337], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8912478677, 13173890525, 13140335077, 4530973161, 13090002417, 17351414265], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17301081605, 21545716241, 21478606369], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6543841289, 2232098829, 2232099853, 1963665425, 1745562641, 1577791505], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1410020373, 1292580885, 1191918613, 1091256345, 1024148505, 957040665], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23641869341, 15018386469, 6411678761, 2099936301, 2099937325, 2032829485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1948944433, 1898613809, 1848283185, 1781175349, 1747621941, 1697291317], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1646960697, 1613407289, 1579853881, 1529523261, 1495969853, 1462416445], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428863041, 1395309633, 1378533441, 1328202821, 1311426629, 1294650437], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1261097033, 1244320841, 1227544649, 1193991245, 22685567233, 26913424657], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26846314785, 26762427701, 30956730701, 30839289193, 1100270394735, 1100253616499], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100236838263, 1100220060027, 1100203281791, 1100186503555, 1100169725319, 621883789], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100136169871, 1100119391635, 1100085836187, 1100069057951, 523874725, 490319277], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4749077941, 4751731125, 4718175677, 8979587525, 8946032077, 8895699417], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13157111265, 4530973161, 13106778605, 17351413241, 17301080581, 21528938005], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2232099853, 1980442641, 1762339857, 1577791505, 1426797589, 1292580885], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1191918613, 1091256345, 1007371289, 940263449, 23641869341, 15018386469], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6411678761, 2099936301, 2066382893, 1999275053, 1915390001, 1865059377], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1814728753, 1747620917, 1697290293, 1663736885, 1596629049, 1563075641], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1529522233, 1479191613, 1445638205, 1412084797, 1378531393, 1344977985], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1311424577, 1277871173, 1261094981, 1227541573, 1193988169, 1177211977], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1160435785, 1126882381, 22702344445, 26930201869, 26846314785, 26762427701], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26661763405, 1100337503583, 1100320725347, 1100303947111, 1100287168875, 30822511981], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100270390639, 1100236835191, 1100220056955, 1100203278719, 1100169723271, 621883789], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100136167823, 1100119389587, 1100085834139, 540650913, 507095465, 4768507313], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4732300729, 4734951865, 8979586501, 8946031053, 13190665689, 13140333029], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4514195949, 13090000369, 17334635005, 17267525133, 21495382557], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1594568721, 1443574805, 1309358101, 1208695829, 1091256345, 1007371289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [940263449, 23641869341, 10723419173, 6411677737, 2116712489, 2099936301], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2032828461, 1965720621, 1898612785, 1831504945, 1781174321, 1714066485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1663735861, 1630182453, 1563074617, 1529521209, 1495967801, 1445637181], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1412083773, 1378530365, 1328199745, 1294646337, 1277870145, 1227539525], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1210763333, 1193987141, 1143656521, 1126880329, 1110104137, 1076550733], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22702344445, 26930201869, 26846314785, 26745650489, 26644986193, 1100337503571], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100354279767, 1100354278747, 1100337500511, 1100303945063, 1100287166827, 1100270388591], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [30805734769, 1100236833143, 1100220054907, 1100186499459, 1100152944011, 605106577], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100119388563, 1100085833115, 540649889, 507094441, 4768506289, 4718173629], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8979585477, 8929252817, 13173887453, 13123554793, 17351412217, 17301079557], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17233969685, 1099549171227, 3988000], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1208695829, 1108033561, 1024148505, 940263449, 23641869341, 10723419173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6411677737, 2116712489, 2099936301, 2032828461, 1965720621, 1881835569], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1814727729, 1764397105, 1697289269, 1646958645, 1596628021, 1546297401], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1495966777, 1462413369, 1412082749, 1378529341, 1344975933, 1294645313], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1261091905, 1244315713, 1193985093, 1177208901, 1143655493, 1110102089], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1093325897, 1059772489, 1026219085, 22702344445, 26913424657, 26829537573], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [26745650489, 1100337503559, 1100371056971, 1100371055955, 1100371054935, 1100354276699], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100320721251, 1100303943015, 1100270387567, 1100253609331, 1100220053883, 1100186498435], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100152942987, 1100119387539, 574204313, 540648865, 4785283501, 4751728053], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8996362689, 8946030029, 8895697369, 13140332005, 13073222133, 17301079557], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099599502863, 17233969685, 1099549170203, 3986976], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [957040665, 23641869341, 10723419173, 6411677737, 2116712489, 2099936301], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2032828461, 1965720621, 1881835569, 1814727729, 1747619889, 1680512053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1630181429, 1579850805, 1529520185, 1479189561, 1445636153, 1378528317], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1344974909, 1311421501, 1261090881, 1227537473, 1210761281, 1160430661], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143654469, 1110101061, 1076547657, 1042994249, 1026218057, 992664653], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [22685567233, 1100337503551, 1100354279747, 1100387833159, 1100387832143, 1100387831123], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100354275675, 1100337497439, 1100303941991, 1100287163755, 1100253608307, 1100220052859], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100186497411, 1100152941963, 590981525, 557426077, 4802060713, 4768505265], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4718172605, 8962807241, 8912474581, 13140332005, 13073222133, 17301079557], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099633057287, 1099599501839, 17233969685, 1099549169179, 3985952], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19346904093, 10723420197, 6411678761, 2099936301, 2032828461, 1965720621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881835569, 1814727729, 1747619889, 1680512053, 1630181429, 1579850805], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1512742969, 1462412345, 1428858937, 1361751101, 1328197693, 1294644285], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244313665, 1210760257, 1177206849, 1143653445, 1110100037, 1093323845], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1042993225, 1026217033, 992663625, 959110221, 1100337503543, 1100371056955], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371055939, 1100404609351, 1100404608335, 1100387830099, 1100354274651, 1100337496415], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100303940967, 1100270385519, 1100236830071, 1100203274623, 1100169719175, 1100119386515], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [574203289, 523870629, 4768505265, 4718172605, 8962807241, 8912474581], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13140332005, 13073222133, 1099633057279, 17301079557, 1099616279051, 1099582723603], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17233969685, 1099532390943, 56860, 56864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15035162657, 6411677737, 2116712489, 2099936301, 2049605677, 1965720621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881835569, 1814727729, 1747619889, 1680512053, 1630181429, 1579850805], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1512742969, 1462412345, 1412081721, 1361751101, 1328197693, 1277867069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1227536449, 1193983041, 1177206849, 1126876229, 1093322821, 1059769413], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026216009, 992662601, 975886409, 942333005, 1100337503539, 1100354279735], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100387833147, 1100387832131, 1100421385543, 1100404607311, 1100371051863, 1100337496415], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100320718179, 1100287162731, 1100253607283, 1100203274623, 1100169719175, 1100136163727], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [574203289, 523870629, 4768505265, 4718172605, 8962807241, 8912474581], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13140332005, 13073222133, 1099616280059, 1099633056259, 17301079557, 1099599500815], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099565945367, 56852, 17217192473, 56856, 56860, 3984928], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10723421221, 2116712489, 2099936301, 2049605677, 1982497837, 1898612785], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831504945, 1764397105, 1680512053, 1630181429, 1579850805, 1512742969], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462412345, 1412081721, 1361751101, 1311420477, 1277867069, 1227536449], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1193983041, 1160429633, 1110099013, 1076545605, 1059769413, 1009438793], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975885385, 959109193, 925555789, 1100337503535, 1100354279731, 1100387833143], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100387832127, 1100404608327, 1100421384523, 1100387829075, 1100354273627, 1100320718179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100287162731, 1100253607283, 1100220051835, 1100169719175, 1100136163727, 574203289], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [523870629, 4768505265, 4718172605, 8962807241, 8895697369, 13123554793], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099616280055, 13056444921, 1099633056255, 17284302345, 1099616278027, 1099582722579], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 56852, 17217192473, 56856, 1099532389919, 16833052], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2116712489, 2099936301, 2066382893, 1999275053, 1898612785, 1831504945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764397105, 1697289269, 1630181429, 1579850805, 1512742969, 1462412345], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1412081721, 1361751101, 1311420477, 1277867069, 1227536449, 1193983041], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160429633, 1110099013, 1076545605, 1042992197, 992661577, 975885385], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942331977, 908778573, 1099698986283, 1100354279727, 1100371055927, 1100404609339], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100421385539, 1100421384523, 1100387829075, 1100354273627, 1100136176987, 1100320718179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100287162731, 1100253607283, 1100220051835, 1100169719175, 624535949, 574203289], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4818837925, 4768505265, 9013139901, 8946030029, 8895697369, 13123554793], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099633057267, 13056444921, 1099633056251, 1099633055239, 17267525133, 1099582722579], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 56852, 16833048, 17200415261, 1099532389919, 16833052], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1999275053, 1915390001, 1848282161, 1781174321, 1697289269, 1646958645], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1596628021, 1529520185, 1479189561, 1428858937, 1361751101, 1311420477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1277867069, 1227536449, 1193983041, 1143652417, 1093321797, 1076545605], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1042992197, 992661577, 959108169, 942331977, 892001357, 1099715763495], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100354279727, 1100387833139, 1100404609339, 1100421385539, 1100421384523, 1100404606287], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371050839, 1100119399771, 1100320718179, 1100287162731, 1100253607283, 1100220051835], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100169719175, 607758737, 557426077, 4802060713, 4751728053, 8996362689], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8946030029, 13173887453, 13106777581, 1099633057263, 1099633056251, 17334635005], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099633055239, 17267525133, 56844, 1099582722579, 56848, 56852], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16833048, 1099532389919, 16833052, 16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1797951537, 1714066485, 1663735861, 1596628021, 1529520185, 1479189561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1428858937, 1361751101, 1328197693, 1277867069, 1227536449, 1193983041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1143652417, 1093321797, 1059768389, 1042992197, 992661577, 959108169], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [925554761, 892001357, 1099698986279, 1099715762475, 1100387833139, 1100404609339], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100421385539, 1100438161735, 1100404606287, 1100371050839, 1100136176983, 1100152953183], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320718179, 1100287162731, 1100253607283, 1100203274623, 1100169719175, 607758737], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [557426077, 4802060713, 4751728053, 8979585477, 8929252817, 13157110241], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099633057263, 1099633056251, 1099633055239, 56844, 1099582722579, 56848], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56852, 16833048, 1099532389919, 16833052, 16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1613405237, 1529520185, 1479189561, 1445636153, 1378528317, 1328197693], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1294644285, 1227536449, 1193983041, 1160429633, 1110099013, 1076545605], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1042992197, 992661577, 959108169, 925554761, 892001357, 1099698986279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099715762475, 1100387833139, 1100404609339, 1100421385539, 1100421384523, 1100387829075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100136176983, 1100354273627, 1100152953183, 1100320718179, 1100287162731, 1100236830071], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100203274623, 1100152941963, 590981525, 557426077, 4802060713, 4734950841], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099633057263, 1099633056251, 1099633055239, 56844, 1099582722579, 56848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56852, 16833048, 1099532389919, 16833052, 16833056], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group15
