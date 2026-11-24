import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 989925385, 6593909771, 2080840717, 1694965775, 1426531343], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1225205777, 1090989073, 990326801, 889664533, 28020586517, 19397104669], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10773620773, 2166912041, 2166913065, 2099805229, 2049474605, 1982366765], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1915258929, 1864928305, 1814597681, 1764267061, 1713936437, 1680383029], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1630052409, 1596499001, 1562945593, 1512614973, 1495838781, 1462285373], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428731969, 1395178561, 1378402369, 1344848965, 1328072773, 1311296581], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1277743177, 1260966985, 1244190793, 1210637389, 27114484973, 14177800441], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [27030597889, 1158688025, 5319436601, 5134886245, 1100303949171, 1100287170935], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100270392699, 1100253614463, 1100236836227, 1100220057991, 1100203279755, 1100186501519], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100169723283, 1100136167835, 607761821, 9161417125, 1100085703079, 557297065], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [523741617, 4785153465, 4751598017, 4718042569, 4684421585, 8929056221], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8895500773, 13140135409, 13089802749, 17334437385, 17267327513, 17216994853], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2298943497, 2131172367, 1694965775, 1409754125, 1225205777, 1090989073], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [973549585, 872887317, 28020586517, 15102137373, 10773619749, 2166911017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2166912041, 2150135849, 2066250797, 1999142957, 1932035117, 1864927281], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1814596657, 1764266033, 1697158197, 1663604789, 1630051381, 1562943545], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1529390137, 1495836729, 1462283325, 1428729917, 1395176509, 1361623105], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1328069697, 1311293505, 1277740101, 1260963909, 1227410501, 1193857097], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1177080905, 1160304713, 1143528525, 27131262185, 27047375101, 1158688025], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [5319436601, 5151663457, 1100354148707, 1100320595299, 1100354147687, 1100337369451], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100320591215, 1100287166839, 1100270388603, 1100253610367, 1100236832131, 1100203276683], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100186498447, 1100152811927, 1100119256479, 1100102478243, 9161417125, 557295017], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [523739569, 4768374205, 4734753221, 4701197773, 8945832409, 8895499749], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13140134385, 13089801725, 8725208589, 17317659149, 17250549277, 1099549040167], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17183439405, 3856940], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1426531341, 1241982993, 1090989073, 973549585, 872887317, 28020586517], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15102137373, 10773619749, 2166911017, 2166912041, 2116581417, 2032696365], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1965588525, 1898480685, 1831372849, 1781042225, 1730711601, 1663603765], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1613273141, 1579719733, 1529389113, 1495835705, 1445505081, 1411951677], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1378398269, 1344844861, 1311291457, 1277738049, 1260961857, 1210631237], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1193855045, 1177078853, 1143525449, 1126749257, 1109973065, 1076419661], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [27131262185, 27047375101, 1158688025, 5302659389, 1100303818067, 1100320594263], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337370459, 1100370923871, 1100370922851, 5134886245, 1100354144615, 1100337366379], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100303942003, 1100287163767, 1100253608319, 1100236830083, 1100203143563, 1100169588115], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100152809879, 590849441, 557293993, 523738545, 4785084857, 4734752197], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4684419537, 8929054173, 8878721513, 13123356149, 13056246277, 1099632926227], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17284103701, 1099599370779, 1099565815331, 17216993829, 3854892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [990326801, 872887317, 28020586517, 15102137373, 10773619749, 2166911017], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2166912041, 2099804201, 2015919149, 1948811309, 1881703469, 1797818417], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1747487793, 1697157169, 1630049333, 1579718709, 1546165301, 1479057465], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1445504057, 1411950649, 1361620029, 1328066621, 1311290429, 1260959809], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1227406401, 1210630209, 1160299589, 1143523397, 1126747205, 1093193801], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1076417609, 1059641417, 1026088013, 27131262185, 27030597889, 1100303818055], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100320594251, 1100337370447, 1100354146643, 1100370922839, 1100404476251, 1100387698015], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100354142567, 1100337364331, 1100303939955, 1100270384507, 1100253475199, 1100219919751], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100186364303, 1100152808855, 607625629, 557292969, 523671985, 4768306621], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4717973961, 8962608597, 8912275937, 13140133361, 13073023489, 1099616148999], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099616147983, 13005913617, 1099616146967, 1099582591519, 17233771041, 56864], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099549036071, 56868, 16833064, 16833068], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [28020587541, 15085361185, 6478653477, 2166911017, 2166912041, 2099804201], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1999141933, 1932034093, 1864926253, 1781041201, 1730710577, 1680379953], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1613272117, 1562941493, 1512610869, 1462280249, 1428726841, 1378396217], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1328065597, 1294512189, 1277735997, 1227405377, 1193851969, 1177075777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1126745157, 1109968965, 1076415557, 1042862153, 1026085961, 1009309769], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [975756365, 1100303818043, 1100320594239, 1100337370435, 1100354146631, 1100387700043], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100387699027, 1100421252439, 1100387696991, 1100370918755, 1100337363307, 1100303938931], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100287029623, 1100253474175, 1100219918727, 1100169586067, 624402841, 590847393], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [540449197, 4785083833, 4734751173, 8979385809, 8929053149, 8861943277], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099616148987, 13089800701, 1099616147971, 1099632924171, 13022690829, 1099632923155], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56852, 56856, 1099582590495, 16833052, 17233771041, 16833056], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099549035047, 16833060, 33609256, 33609260], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [23708846105, 10790395937, 6478654501, 2166912041, 2099804201, 1999141933], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1932034093, 1864926253, 1781041201, 1713933361, 1663602737, 1596494901], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546164277, 1495833653, 1445503033, 1395172409, 1361619001, 1311288381], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1277734973, 1244181565, 1193850945, 1160297537, 1143521345, 1093190725], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1076414533, 1042861125, 1009307721, 992531529, 975755337, 942201933], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100287040819, 1100303817015, 1100337370427, 1100354146623, 1100370922819, 1100387699019], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100421252431, 1100421251415, 1100404473179, 1100370917731, 1100337362283, 1100303806835], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100270251387, 1100236695939, 1100203140491, 1100152807831, 607624605, 557226409], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4801861045, 4751528385, 8996163021, 8929053149, 8861943277, 1099632926191], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632925175, 13089800701, 1099616146947, 1099632923147, 13022690829, 56844], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632922131, 56848, 16833044, 16833048, 1099582589471, 33609244], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17233771041, 33609248, 33609252, 1099532191275, 50385448, 50385452], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [15102137373, 10773619749, 2166911017, 2166912041, 2099804201, 2015919149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1932034093, 1864926253, 1781041201, 1713933361, 1663602737, 1596494901], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546164277, 1495833653, 1428725817, 1395172409, 1344841785, 1294511165], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1260957757, 1227404349, 1177073729, 1143520321, 1109966913, 1076413509], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1042860101, 1026083909, 975753289, 958977097, 942200905, 908647501], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100287040811, 1100303817007, 1100337370419, 1100354146615, 1100370922815, 1100387699011], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100404475211, 1100438028623, 1100421250391, 1100387694943, 1100354139495, 1100320584047], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100287028599, 1100253473151, 1100203140491, 1100169585043, 607624605, 557226409], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4801861045, 4751528385, 4701195725, 8929053149, 1099632926183, 8861943277], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632925167, 1099632924155, 13089800701, 1099632923139, 56836, 56840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632922127, 16833036, 13005913617, 16833040, 1099599301143, 16833044], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33609240, 33609244, 17233771041, 1099565745699, 50385440, 50385444], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50385448, 3785260, 3852844, 67161644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [10790395937, 6478654501, 2166912041, 2116581417, 2015919149, 1948811309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1864926253, 1781041201, 1730710577, 1663602737, 1596494901, 1546164277], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1495833653, 1428725817, 1378395193, 1344841785, 1277733949, 1244180541], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1210627133, 1160296513, 1126743105, 1109966913, 1059636293, 1026082885], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1009306693, 958976073, 942199881, 925423689, 875093069, 1100287040803], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100303817003, 1100320593199, 1100354146611, 1100354145595, 1100387699007, 1100404475207], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100421251407, 1100438027603, 1100404472155, 1100370916707, 1100337361259, 1100303805811], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100253473151, 1100219917703, 1100169585043, 607624605, 557226409, 4801861045], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4751528385, 8979385809, 8929053149, 1099632926175, 1099632925163, 8861943277], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632924147, 1099632923135, 56828, 13073023489, 56832, 1099649699335], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56836, 16833032, 16833036, 13005913617, 1099599301139, 33609232], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33609236, 33609240, 1099582522911, 50385436, 50385440, 17216993829], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [50385444, 1099532190251, 1099532257835, 67161640, 67161644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6478654501, 2166912041, 2133358633, 2032696365, 1948811309, 1881703469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1797818417, 1730710577, 1663602737, 1596494901, 1546164277, 1495833653], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1428725817, 1378395193, 1344841785, 1277733949, 1244180541, 1210627133], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160296513, 1126743105, 1093189697, 1042859077, 1009305669, 992529477], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942198857, 925422665, 891869257, 858315853, 1100287040799, 1100320594211], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320593195, 1100354146607, 1100370922807, 1100387699003, 1100404475203, 1100438028619], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100438027603, 1100404472155, 1100370916707, 1100337361259, 1100303805811, 1100253473151], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100219917703, 1100169585043, 607624605, 557226409, 4801861045, 4751528385], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8979385809, 1099632926171, 8912275937, 1099616147943, 1099632924143, 13140133361], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632923131, 56824, 56828, 13073023489, 16833024, 1099632922119], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16833028, 16833032, 1099599301135, 33609228, 33609232, 12989136405], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33609236, 1099599300123, 50385432, 50385436, 50385440, 1099549035047], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67161636, 17200216617, 1099532190251, 67161640, 67161644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2150135849, 2049473581, 1965588525, 1898480685, 1814595633, 1747487793], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1680379953, 1613272117, 1546164277, 1495833653, 1428725817, 1378395193], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1344841785, 1277733949, 1244180541, 1210627133, 1143519297, 1109965889], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1076412481, 1042859077, 1009305669, 975752261, 942198857, 908645449], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [891869257, 841538637, 1100287040795, 1100303816995, 1100320593191, 1100337369391], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100370922803, 1100387699003, 1100404475203, 1100438028615, 1100454804815, 1100421249367], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100370916707, 1100337361259, 1100303805811, 1100253473151, 1100219917703, 657957265], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [607624605, 557226409, 4785083833, 4734751173, 8962608597, 1099632926167], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632925155, 8895498725, 1099632924139, 13123356149, 1099632923127, 56820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56824, 56828, 1099632922115, 16833024, 13056246277, 16833028], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33609224, 1099599301135, 33609228, 33609232, 50385428, 17267326489], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099599300123, 50385432, 50385436, 67161632, 1099548967463, 1099549035047], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67161636, 67161640, 17183439405, 67161644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1898480685, 1814595633, 1747487793, 1697157169, 1613272117, 1562941493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1512610869, 1445503033, 1395172409, 1344841785, 1277733949, 1244180541], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1210627133, 1143519297, 1109965889, 1076412481, 1026081861, 1009305669], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [975752261, 925421641, 908645449, 875092041, 841538637, 1100287040795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100303816991, 1100320593191, 1100354146603, 1100370922803, 1100387699003, 1100421252415], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438028615, 1100454804815, 1100421249367, 1100370916707, 1100337361259, 1100303805811], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253473151, 1100203140491, 641180053, 590847393, 540449197, 4785083833], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4717973961, 8962608597, 1099616148951, 1099632925151, 8895498725, 1099632924139], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 13123356149, 1099632923127, 56820, 56824, 16833020], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632922115, 16833024, 16833028, 33609224, 1099582523919, 33609228], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33609232, 50385428, 1099599300123, 50385432, 50385436, 1099549035043], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67161632, 1099548967463, 67161636, 67161640, 83937836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1697157169, 1630049333, 1562941493, 1512610869, 1445503033, 1395172409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1344841785, 1294511165, 1244180541, 1210627133, 1160296513, 1109965889], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1076412481, 1026081861, 992528453, 975752261, 925421641, 891868233], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [875092041, 824761421, 1100287040791, 1100303816991, 1100337370403, 1100354146603], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100370922803, 1100404476215, 1100421252415, 1100454805831, 1100454804815, 1100404472155], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100370916707, 1100337361259, 1100287028599, 1100253473151, 1100203140491, 641180053], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [590847393, 540449197, 4768306621, 4717973961, 1099632926163, 1099632925151], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099632924139, 56816, 1099632923127, 56820, 56824, 16833020], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632922115, 16833024, 16833028, 33609224, 1099582523919, 33609228], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [33609232, 50385428, 1099599300123, 50385432, 50385436, 1099549035043], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67161632, 67161636, 1099532190251, 67161640, 83937836], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1529388085, 1445503033, 1411949625, 1361619001, 1294511165, 1260957757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1210627133, 1160296513, 1126743105, 1076412481, 1026081861, 1009305669], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [975752261, 925421641, 891868233, 875092041, 824761421, 1100287040791], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100303816991, 1100337370403, 1100354146603, 1100370922803, 1100387699003, 1100421252415], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100454805831, 1100438027603, 1100404472155, 1100370916707, 1100320584047, 1100287028599], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100236695939, 641181069, 641180053, 574070181, 1099632926163, 1099632925151], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099632924139, 56816, 1099632923127, 56820, 56824, 16833020], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099632922115, 16833024, 16833028, 33609224, 1099599301135, 33609228], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33609232, 50385428, 1099599300123, 50385432, 50385436, 67161632], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099549035047, 67161636, 20555305, 1099532190251, 67161640, 67161644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group12
