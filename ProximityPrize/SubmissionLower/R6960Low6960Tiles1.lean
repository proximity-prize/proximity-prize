import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass1

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 989925387, 536941577, 1946490889, 1762008077, 1426464781], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15184765965, 6561281045, 2266315797, 2199207961, 2064991257, 1947551769], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [15118650397, 15102270497, 10790530085, 2183821353, 2167045165, 2133491757], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2083161133, 1999276081, 1948945457, 1898614833, 1831506997, 1797953589], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1764400181, 1697292345, 1663738937, 1630185529, 1579854909, 1563078717], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1529525309, 1479194689, 1462418497, 1445642305, 1395311685, 1378535493], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1361759301, 1328205897, 1311429705, 1294653513, 1261100109, 1244323917], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14647760013, 18489741563, 1100286845307, 1100270132607, 1100253354371, 1100236576135], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100219732363, 1100202954127, 1100186175891, 1100169332119, 1100135776671, 1100118998435], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100102220199, 1100068664751, 1100035109303, 1100018331067, 1099984841155, 1099951285707], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099917664723, 355704285, 322148837, 13172492781, 288593389, 4533228025], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4482895365, 17350018569, 4432431633, 8660289057, 17215799849, 8609956397], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1980045323, 1795562511, 1426464783, 10889798669, 6578057233, 2266314773], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2266315797, 2182430745, 2048214041, 1913997337, 15118650397, 15102270497], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6495562789, 2183820329, 2183821353, 2150267949, 2083160109, 2032829485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1948944433, 1898613809, 1848283185, 1781175349, 1747621941, 1697291317], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1646960697, 1613407289, 1579853881, 1529523261, 1495969853, 1462416445], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428863041, 1395309633, 1378533441, 1328202821, 1311426629, 1294650437], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1261097033, 1244320841, 1227544649, 1193991245, 1177215053, 9446826341], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100051964267, 1100068740463, 1100085516659, 1100085515639, 1100102291835, 1100119068031], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100135844227, 1100119000455, 1100118999439, 1100135775635, 1100152551835, 1100135773599], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100102218151, 1100068662703, 1100035107255, 13372693949, 1100001551807, 1099967996359], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099934440911, 372480473, 338925025, 13204920805, 13206047205, 288592365], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099548713455, 1099531935223, 4533227001, 57848, 1099531934207, 16834044], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099548710403, 16834048, 17366795781, 4482763269, 33610244, 1099548709387], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [33610248, 50386444, 1099548708371, 50386448, 4415653397, 67162644], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099582260763, 1099548707355, 67162648, 83938844, 8660288033, 1099582259747], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [83938848, 17232577061, 100715044, 1099548704299, 100715048, 117491244], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [8593178161, 117491248], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [15184765965, 6561281045, 2266315797, 2182430745, 2048214041, 1913997337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15118650397, 15102270497, 6495562789, 2183820329, 2183821353, 2116713517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2049605677, 1982497837, 1915390001, 1865059377, 1797951537, 1747620917], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1697290293, 1646959669, 1596629049, 1563075641, 1529522233, 1479191613], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1445638205, 1412084797, 1361754177, 1344977985, 1311424577, 1277871173], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1261094981, 1227541573, 1193988169, 1177211977, 1160435785, 1126882381], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1110106189, 1100051964251, 1100068740447, 1100085516643, 1100085515623, 1100102291819], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100119068015, 1100119066999, 1100102223227, 1100118999423, 1100135775623, 1100152551819], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100169328019, 1100152549787, 1100118994339, 1100085438891, 1100051883443, 1100018327995], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099984772547, 1099934439887, 372479449, 1099531936223, 338924001, 13206047205], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099531935207, 57828, 57832, 1099531934191, 16834028, 4566781425], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099548710387, 16834032, 33610228, 1099548709371, 33610232, 221350397], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50386428, 1099548708355, 50386432, 17366795781, 67162628, 4465985033], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099582260747, 1099548707339, 67162632, 83938828, 1099582259731, 83938832], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715028, 4398875161, 100715032, 1099531861535, 117491228, 117491232], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [17232577061, 1099548637735, 1099548704295, 134267428, 8626732585, 134267432], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [134267436, 3454512, 167819824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [6578057233, 2266314773, 2266315797, 2199207961, 2048214041, 1913997337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15118650397, 15102270497, 6495562789, 2183820329, 2183821353, 2099936301], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2032828461, 1965720621, 1881835569, 1831504945, 1781174321, 1714066485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1663735861, 1613405237, 1563074617, 1512743993, 1479190585, 1428859965], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1395306557, 1361753149, 1328199745, 1294646337, 1261092929, 1227539525], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1210763333, 1177209925, 1143656521, 1126880329, 1110104137, 1076550733], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1059774541, 1100051964239, 1100051963219, 1100068739415, 1100085515611, 1100102291807], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100119068003, 1100119066987, 1100102223215, 1100118999411, 1100135775611, 1100135774595], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100169328007, 1100186104207, 1100169325975, 1100135770527, 1100102215079, 1100051882419], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100018326971, 1099967994311, 1099917661651, 1099531936211, 1099531935191, 57816], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [355701213, 1099531934175, 16834012, 16834016, 13206047205, 1099531933159], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610212, 305368553, 33610216, 1099531932143, 50386412, 50386416], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [254904821, 1099531931127, 67162612, 67162616, 1099582260735, 1099548707327], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938812, 83938816, 17366795781, 4482762245, 1099548639751, 83938820], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715016, 100715020, 1099531861523, 1099531928083, 117491216, 4415652373], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [117491220, 1099548637723, 151043608, 151043612, 151043616, 8643509797], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099548636711, 167819812, 17215799849, 167819816, 167819820, 3453488], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [184596016], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2266315797, 2215985177, 2064991257, 1930774553, 15118650397, 15102270497], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6495562789, 2183820329, 2183821353, 2099936301, 2016051245, 1948943405], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1881835569, 1814727729, 1764397105, 1697289269, 1646958645, 1596628021], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1529520185, 1495966777, 1462413369, 1395305533, 1361752125, 1328198717], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1294645313, 1261091905, 1227538497, 1193985093, 1160431685, 1143655493], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1110102089, 1076548681, 1059772489, 1026219085, 1009442893, 1100035187011], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100051963207, 1100068739403, 1100085515599, 1100085514583, 1100102290779, 1100119066975], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100001428839, 1100118999403, 1100118998387, 1100135774587, 1100169327999, 1100186104199], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100202880399, 1100152547739, 1100118992291, 1100085436843, 1100035104183, 1099984771523], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548713411, 1099531935179, 1099934438863, 57804, 1099531934163, 16834000], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16834004, 372478425, 1099531933147, 33610200, 1099632526815, 33610204], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099531932131, 50386400, 322145765, 50386404, 13189269993, 1099548708331], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162600, 67162604, 1099548707315, 67162608, 254904821, 83938804], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938808, 1099531862527, 1099531929087, 100715004, 4499539457, 100715008], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099548638727, 134267396, 17350018569, 134267400, 3523084, 117491212], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4432429585, 1099548637715, 151043600, 151043604, 151043608, 1099548636703], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [167819804, 167819808, 8643509797, 167819812, 1099548635691, 184596008], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [17199022637, 184596012, 184596016], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 140 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1947551769, 15118650397, 15102270497, 6495562789, 2183820329, 2183821353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2099936301, 2016051245, 1948943405, 1865058353, 1797950513, 1747619889], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1680512053, 1630181429, 1579850805, 1512742969, 1479189561, 1428858937], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378528317, 1344974909, 1311421501, 1261090881, 1227537473, 1193984065], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1160430661, 1126877253, 1110101061, 1076547657, 1042994249, 1026218057], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [992664653, 975888461, 1100035187003, 1100051963199, 1100068739395, 1100085515591], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100085514575, 1100102290771, 1100119066967, 1100001428831, 1100018205027, 1100118998379], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100135774579, 1100152550779, 1100169326979, 1100186103179, 1100186102163, 1100135769503], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100102214055, 1100051881395, 1099531936187, 1100001548735, 1099531935171, 57792], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57796, 1099951216075, 1099531934155, 16833992, 16833996, 1099531933139], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610192, 389255637, 1099632526807, 33610196, 1099531932123, 50386392], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632525791, 50386396, 338922977, 1099531931107, 67162592, 67162596], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099548707307, 83938792, 13172492781, 83938796, 271682033, 83938800], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099531929079, 100714996, 100715000, 1099548638719, 134267388, 4499539457], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [134267392, 134267396, 1099548637707, 151043592, 151043596, 4432429585], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [151043600, 1099548636695, 167819796, 167819800, 167819804, 1099548635683], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [184596000, 4348542501, 184596004, 184596008, 1099531857455, 201372204], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19414012957, 10790529061, 2183820329, 2183821353, 2099936301, 2032828461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1948943405, 1865058353, 1797950513, 1747619889, 1680512053, 1613404213], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1563073589, 1512742969, 1462412345, 1428858937, 1361751101, 1328197693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1294644285, 1244313665, 1210760257, 1177206849, 1126876229, 1110100037], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1076546629, 1042993225, 1026217033, 992663625, 959110221, 942334029], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100035186995, 1100051963191, 1100068739387, 1100068738371, 1100085514567, 1100102290763], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100119066963, 1100001428823, 1100018205023, 1100018204007, 1100135774575, 1100152550775], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169326975, 1100186103175, 1100186102163, 1100152546715, 1100102214055, 1100068658607], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099531936179, 1100018325947, 1099531935163, 57784, 57788, 1099531934147], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16833984, 16833988, 1099951216075, 1099531933131, 33610184, 1099632526799], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610188, 1099531932115, 50386384, 389255637, 50386388, 1099632525787], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099548708315, 67162584, 67162588, 338922977, 1099649301987, 67162592], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099531930087, 83938788, 83938792, 117491180, 271682033, 1099531929075], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [100714992, 100714996, 134267384, 134267388, 4499539457, 134267392], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099548637703, 151043588, 151043592, 151043596, 1099548636691, 167819792], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4415652373, 167819796, 167819800, 1099548635679, 184595996, 184596000], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [8643509797, 184596004, 1099548634667, 201372200, 201372204, 201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15102271521, 6478786601, 2183821353, 2116713517, 2032828461, 1965720621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881835569, 1814727729, 1747619889, 1680512053, 1613404213, 1563073589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1495965753, 1462412345, 1412081721, 1361751101, 1311420477, 1277867069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1227536449, 1193983041, 1160429633, 1110099013, 1093322821, 1059769413], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026216009, 992662601, 975886409, 925555789, 908779597, 1100035186987], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100051963183, 1100051962167, 1100068738363, 1100068737347, 1100102290759, 1100102289743], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100001428819, 1100018205019, 1100018204003, 1100135774571, 1100152550771, 1100169326971], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100186103175, 1100202879375, 1100152546715, 1100118991267, 1099531936171, 1100068658607], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099531935155, 57776, 57780, 1100018325947, 1099531934139, 16833976], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [16833980, 1099548710339, 33610176, 33610180, 1099951216075, 1099632526795], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099548709323, 33610184, 50386380, 50386384, 389255637, 1099632525783], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099531931095, 67162580, 67162584, 1099649301983, 1099548707295, 83938780], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938784, 322145765, 83938788, 117491176, 117491180, 3524080], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [100714992, 254904821, 134267380, 134267384, 134267388, 1099548637699], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043584, 4482762245, 151043588, 151043592, 1099548636687, 167819788], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [167819792, 4415652373, 167819796, 1099548635675, 184595992, 184595996], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [184596000, 201372196, 8626732585, 1099548634667, 201372200, 201372204], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 140 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6495562789, 2183820329, 2183821353, 2133490733, 2049605677, 1965720621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1881835569, 1814727729, 1747619889, 1680512053, 1630181429, 1563073589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1495965753, 1462412345, 1412081721, 1344973885, 1311420477, 1277867069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1227536449, 1193983041, 1160429633, 1110099013, 1076545605, 1042992197], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009438793, 975885385, 959109193, 908778573, 892002381, 1100035186983], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100051963179, 1100051962163, 1100068738359, 1100068737343, 1100102290755, 1100102289739], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099984651603, 1100001427803, 1100018204003, 1100118997355, 1100152550771, 1100169326971], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100202880387, 1100202879375, 1100152546715, 1100118991267, 1099531936167, 1100068658607], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099531935151, 57772, 57776, 1099531934135, 16833972, 16833976], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100001548735, 1099531933119, 33610172, 33610176, 1099632526791, 1099548709319], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386372, 1099951216075, 50386376, 50386380, 1099632525779, 1099531931091], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162576, 389255637, 67162580, 1099548707291, 83938776, 1099632524767], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938780, 83938784, 322145765, 117491172, 117491176, 117491180], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267376, 254904821, 134267380, 134267384, 1099548637695, 151043580], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043584, 4482762245, 151043588, 167819784, 1099548636687, 167819788], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [167819792, 167819796, 4398875161, 1099548635675, 184595992, 184595996], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [184596000, 201372196, 1099548634667, 201372200, 8609955373, 201372204], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2183821353, 2150267949, 2066382893, 1982497837, 1898612785, 1831504945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764397105, 1680512053, 1630181429, 1579850805, 1512742969, 1462412345], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1412081721, 1344973885, 1311420477, 1277867069, 1210759233, 1177205825], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1143652417, 1093321797, 1059768389, 1042992197, 992661577, 959108169], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942331977, 892001357, 875225165, 1100035186979, 1100051963175, 1100051962159], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100068738355, 1100085514555, 1100085513539, 1100119066951, 1100001428815, 1100018205015], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100034981215, 1100051757415, 1100152550771, 1100169326971, 1100202880387, 1100202879375], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100152546715, 1099531936163, 1100102214055, 1099531935147, 57768, 57772], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100051881395, 1099531934131, 16833968, 16833972, 1099548710331, 33610168], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100001548735, 33610172, 33610176, 1099632526791, 1099531932103, 50386372], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099951216075, 50386376, 1099548708303, 67162572, 1099632525779, 67162576], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162580, 372478425, 1099548707291, 83938776, 1099632524767, 83938780], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938784, 117491172, 305368553, 1099632523755, 117491176, 117491180], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267376, 134267380, 238127609, 134267384, 151043580, 151043584], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043588, 4465985033, 167819784, 1099531859471, 167819788, 167819792], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [184595988, 1099548635675, 184595992, 4382097949, 184595996, 184596000], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [201372196, 1099548634667, 201372200, 201372204, 8593178161, 201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1999275053, 1915390001, 1848282161, 1781174321, 1697289269, 1646958645], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1579850805, 1512742969, 1462412345, 1412081721, 1361751101, 1311420477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1277867069, 1210759233, 1177205825, 1143652417, 1093321797, 1059768389], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1026214981, 992661577, 959108169, 925554761, 892001357, 858447949], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100035186975, 1100035185959, 1100051962155, 1100068738355, 1100068737339, 1100102290751], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100119066951, 1100001428815, 1100001427799, 1100018203999, 1100051757415, 1100152550771], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100169326971, 1100186103175, 1100202879375, 1100152546715, 1099531936159, 1100102214055], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099531935143, 57764, 57768, 1099548711343, 16833964, 1100051881395], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16833968, 16833972, 1099531933115, 33610168, 33610172, 1099984771523], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548709315, 50386368, 1099632526791, 50386372, 50386376, 422811085], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099649302991, 1099531931087, 67162572, 67162576, 83938772, 1099649301979], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099531930075, 83938776, 355701213, 83938780, 100714976, 117491172], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632523755, 117491176, 4583558637, 117491180, 134267376, 134267380], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267384, 221350397, 151043580, 151043584, 151043588, 167819784], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4449207821, 1099548636687, 167819788, 167819792, 167819796, 1099548635675], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [184595992, 184595996, 184596000, 201372196, 1099548634667, 201372200], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [201372204, 201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1781174321, 1714066485, 1646958645, 1596628021, 1529520185, 1479189561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1428858937, 1361751101, 1311420477, 1277867069, 1227536449, 1177205825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1143652417, 1093321797, 1059768389, 1026214981, 975884361, 959108169], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [925554761, 892001357, 858447949, 1100018409759, 1100035185959, 1100051962155], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100068738355, 1100085514551, 1100102290751, 1100119066951, 1100001428815, 1100018205015], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100034981215, 1100135774571, 1100152550771, 1100186104187, 1100202880391, 1100186102163], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099548713371, 1100135769503, 1099531935143, 57764, 1100085436843, 57768], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099531934127, 16833964, 16833968, 1100035104183, 33610164, 1099531933115], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33610168, 33610172, 406034881, 1099548709315, 50386368, 1099632526791], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50386372, 50386376, 1099531931087, 67162572, 406033873, 1099632525779], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162576, 83938772, 1099531930075, 83938776, 355701213, 1099632524767], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938780, 100714976, 117491172, 117491176, 117491180, 134267376], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [134267380, 134267384, 151043580, 1099531860483, 151043584, 151043588], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [167819784, 1099548636687, 167819788, 167819792, 167819796, 184595992], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099548635679, 184595996, 184596000, 37001765, 184596004, 201372200], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099531857455, 201372204, 39472, 201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1596628021, 1529520185, 1479189561, 1428858937, 1361751101, 1328197693], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1277867069, 1227536449, 1177205825, 1143652417, 1093321797, 1059768389], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1026214981, 975884361, 959108169, 925554761, 875224141, 858447949], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018409759, 1100035185955, 1100051962155, 1100051961139, 1100085514551, 1100102290751], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100119066951, 1100001428815, 1100018205015, 1100034981215, 1100135774571, 1100152550771], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100169326975, 1100202880391, 1100186102163, 1099531936155, 372483485, 1099548712355], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57760, 57764, 389259689, 57768, 1099531934127, 16833964], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [16833968, 406035893, 1099548710327, 33610164, 33610168, 33610172], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099548709315, 50386368, 1099632526791, 50386372, 50386376, 1099531931087], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [67162572, 1099632525779, 67162576, 83938772, 1099531930075, 83938776], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632524767, 83938780, 100714976, 117491172, 117491176, 117491180], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [134267376, 134267380, 37004793, 134267384, 151043580, 1099548637699], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [151043584, 42500, 151043588, 37003785, 42504, 151043592], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [42508, 1099548636687, 167819788, 42512, 167819792, 16818708], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [167819796, 20225561, 16818712, 184595992, 16818716, 1099548635679], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [184595996, 33594912, 184596000, 33594916, 184596004, 33594920], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [201372200, 33594924, 1099531857455, 201372204, 33594928, 201372208], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 140 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group1
