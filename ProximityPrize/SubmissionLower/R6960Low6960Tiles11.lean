import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass11

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2164329477, 973148169, 6443045897, 2131368973, 2131369997, 1997153293], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1745496081, 1560947729, 1409953809, 1275737109, 1175074837, 1091189781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1007304729, 940196889, 889866265, 822758429, 789205021, 755651613], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [705320993, 671767585, 654991393, 14917592101, 6310884393, 1999141933], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1999142957, 1948812333, 1881704497, 1831373873, 1781043249, 1730712629], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1680382005, 1646828597, 1596497977, 1562944569, 1529391161, 1495837757], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1462284349, 1445508157, 1395177537, 1378401345, 1361625153, 1311294533], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1294518341, 1277742149, 1244188745, 1227412553, 1210636361, 1177082957], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1177083981, 14263279809, 18541468869, 18507913421, 18474357973, 22735769821], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22702214373, 22651881713, 9748156661, 26896516349, 26829406477, 26762296605], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [39563966769, 39463302473, 39345860965, 1100186705259, 1100186706283, 1100169927023], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100153148787, 1100136370551, 1100119526779, 591120765, 574342529, 39194865033], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4835754377, 4818976141, 4802197905, 9063609753, 9046831517, 13308243365], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13291465129, 13257909681, 39010314677, 17519321529, 17485766081, 21747177929], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4516386261, 8777798109, 8727465449, 38775432685, 12972100085, 12921767425], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6443046921, 2131369997, 1997153293, 1745496081, 1560947729, 1409953809], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1258959893, 1158297621, 1057635349, 973750297, 906642457, 856311833], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [789203997, 738873373, 705319965, 654989345, 621435937, 587882529], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [10622624805, 6310883369, 2015918121, 1999141933, 1965588525, 1898480685], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1831372849, 1781042225, 1730711601, 1663603765, 1630050357, 1596496949], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1546166329, 1512612921, 1479059513, 1428728893, 1395175485, 1378399293], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1328068673, 1311292481, 1277739073, 1244185669, 1227409477, 1210633285], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1177079881, 1160303689, 1143527497, 1109974093, 1093197901, 14330388657], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14296833209, 18558245057, 18524689609, 18491134161, 22735768797, 22685436137], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22635103477, 26862960901, 26795851029, 39580743981, 39480079685, 1100270592343], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100253814107, 1100237035871, 1100220257635, 39345860965, 1100203479399, 1100186635627], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100169857391, 1100153079155, 624673141, 3915132, 4869306753, 39194865033], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4835751305, 4818973069, 9080384917, 9046829469, 13308241317, 13274685869], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [39010314677, 17536097717, 17502542269, 4583495109, 4533162449, 8777797085], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [8727464425, 38775432685, 12972099061, 12904989189], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2030707725, 1762273297, 1560947729, 1409953809, 1258959893, 1158297621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1057635349, 956973081, 889865241, 822757401, 755649565, 705318941], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [671765533, 621434913, 587881505, 554328097, 10622624805, 6310883369], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2015918121, 1982364717, 1915256877, 1864926253, 1797818417, 1730710577], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1697157169, 1630049333, 1579718709, 1546165301, 1495834681, 1462281273], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428727865, 1378397245, 1344843837, 1311290429, 1277737025, 1244183617], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1227407425, 1193854021, 1177077829, 1143524421, 1109971017, 1093194825], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1076418633, 1042865229, 1042866253, 14363943081, 14330387633, 18591799481], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18558244033, 18524688585, 22769323221, 22718990561, 22651880689, 26879738113], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [26795851029, 39580743981, 39480079685, 1100320922955, 1100320923979, 1100304144719], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100287366483, 1100270588247, 1100135714139, 1100135713123, 39345860965, 1100152489319], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100186632555, 658226541, 624671093, 607892857, 4869304705, 39194865033], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4835749257, 9097161105, 9063605657, 13325017505, 13291462057, 13257906609], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [38993537465, 4617049533, 4566716873, 4533161425, 8761018849, 8710686189], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099616210419, 38741878261, 12955320825, 1099582654971, 1099549099523, 12888210953], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1426731025, 1275737109, 1158297621, 1057635349, 956973081, 889865241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [822757401, 755649565, 705318941, 654988317, 604657697, 571104289], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [537550881, 10622624805, 6310883369, 2015918121, 1965587501, 1898479661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1831371821, 1764263985, 1713933361, 1663602737, 1596494901, 1546164277], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1512610869, 1462280249, 1411949625, 1378396217, 1328065597, 1311289405], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1277735997, 1227405377, 1210629185, 1177075777, 1143522373, 1126746181], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1093192773, 1059639369, 1042863177, 1026086985, 992533581, 975757389], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14380720293, 14347164845, 14313609397, 18575021245, 18524688585, 22769323221], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22718990561, 22651880689, 26879738113, 26795851029, 39580743981, 1100388032827], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100371254591, 1100354476355, 1100337698119, 39463302473, 1100320919883, 1100135714127], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100135713111, 1100169266523, 1100186042719, 1100186041703, 39329083753, 675002729], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [641447281, 3912056, 4886080893, 4852525445, 9113937293, 9063604633], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13325016481, 13291461033, 355636661, 4600271297, 4549938637, 8794573273], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8744240613, 1099666542055, 1099632986607, 12972098037, 1099582653947, 1099549098499], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [12904988165, 3915272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1074412565, 973750297, 906642457, 839534617, 755649565, 705318941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [654988317, 604657697, 554327073, 520773665, 10622624805, 6310883369], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2015918121, 1965587501, 1898479661, 1831371821, 1747486769, 1697156145], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1646825521, 1579717685, 1529387061, 1479056437, 1428725817, 1395172409], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1361619001, 1311288381, 1277734973, 1244181565, 1193850945, 1177074753], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1143521345, 1109967941, 1076414533, 1059638341, 1026084937, 1009308745], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [992532553, 942201933, 942202957, 14397497505, 14363942057, 14313609397], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18575021245, 18524688585, 22769323221, 22702213349, 22635103477, 26862960901], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26779073817, 1100421586227, 1100421587251, 1100388030779, 1100371252543, 1100354474307], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100135714119, 1100152490315, 1100152489299, 1100186042711, 1100186041695, 1100219595107], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [675001705, 641446257, 4902858105, 4869302657, 9130714505, 9097159057], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [9063603609, 13308238245, 372413873, 4617048509, 4566715849, 8811350485], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099700096479, 8744240613, 1099666541031, 1099632985583, 8677130741, 1099582652923], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099549097475, 12904988165], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 130 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [839534617, 772426781, 705318941, 654988317, 604657697, 554327073], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [520773665, 10622624805, 6310883369, 2015918121, 1965587501, 1881702445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1814594605, 1747486769, 1680378929, 1630048305, 1562940469, 1512609845], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1462279221, 1411948601, 1378395193, 1328064569, 1277733949, 1244180541], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1210627133, 1177073729, 1143520321, 1109966913, 1076413509, 1042860101], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1026083909, 992530505, 958977097, 942200905, 908647501, 891871309], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [14397497505, 14363942057, 18608576693, 18575021245, 18524688585, 22752546009], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22702213349, 1100471918887, 1100455140651, 1100438362415, 1100421584179, 1100388028731], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100135714111, 1100152490307, 1100169266507, 1100186042703, 1100202818903, 1100202817887], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100219594083, 675000681, 641445233, 4902857081, 4852524421, 9113936269], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [9080380821, 13325015457, 389191085, 338858425, 4583493061, 4516383189], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099733650903, 1099700095455, 8761017825, 1099649762795, 8693907953, 1099616207347], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099565874687, 12904988165, 1099532319239], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [671765533, 604657697, 571104289, 520773665, 10622624805, 6310883369], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2015918121, 1965587501, 1898479661, 1831371821, 1747486769, 1680378929], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1630048305, 1562940469, 1512609845, 1462279221, 1395171385, 1361617977], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1311287353, 1260956733, 1227403325, 1193849917, 1143519297, 1126743105], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1093189697, 1042859077, 1026082885, 992529477, 958976073, 942199881], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [908646473, 875093069, 858316877, 14397497505, 14347164845, 18608576693], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18558244033, 1100488696095, 1100488695075, 1100471916839, 1100438361391, 1100421583155], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100152491319, 1100152490303, 1100186043715, 1100186042699, 1100202818899, 1100219595095], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100236371295, 1100202815847, 658222445, 4919634293, 4869301633, 9130713481], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [9080380821, 13325015457, 389191085, 338858425, 4583493061, 1099750428115], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4516383189, 1099716872667, 8744240613, 1099666540007, 1099632984559, 8677130741], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099582651899, 1099549096451, 12904988165, 4055560], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 130 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [537550881, 10622624805, 6310883369, 2015918121, 1982364717, 1898479661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1831371821, 1747486769, 1680378929, 1630048305, 1562940469, 1512609845], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1462279221, 1395171385, 1344840761, 1311287353, 1260956733, 1210626109], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1177072701, 1126742081, 1109965889, 1076412481, 1026081861, 1009305669], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [975752261, 942198857, 908645449, 891869257, 858315853, 841539661], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [14380720293, 1100488696091, 1100505472287, 1100488694051, 1100471915815, 1100438360367], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100152491315, 1100152490299, 1100186043711, 1100186042695, 1100202818895, 1100236372307], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100253148507, 1100219593059, 658222445, 4919634293, 4886078845, 9130713481], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9080380821, 13325015457, 389191085, 338858425, 4583493061, 1099767205327], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4516383189, 1099733649879, 1099683317219, 8744240613, 1099649761771, 8677130741], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099599429111, 1099549096451, 1099532460551, 12888210953], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 130 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10622626853, 2015918121, 1982364717, 1915256877, 1848149037, 1764263985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1697156145, 1630048305, 1562940469, 1512609845, 1462279221, 1395171385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1344840761, 1311287353, 1244179517, 1210626109, 1177072701, 1126742081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1093188673, 1059635265, 1009304645, 992528453, 958975045, 925421641], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [891868233, 875092041, 841538637, 807985229, 1100505473299, 1100505472283], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100505471263, 1100488693027, 1100455137579, 1100152491311, 1100169267511, 1100186043707], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100202819907, 1100219596107, 1100219595091, 1100253148507, 1100219593059, 674999657], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4919634293, 4886078845, 9130713481, 9080380821, 13325015457, 389191085], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4633825721, 4566715849, 1099783982539, 1099733649879, 8794573273, 1099700094431], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [8727463401, 1099649761771, 1099599429111, 8660353529, 1099565873663, 1099532460547], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [12888210953, 4054536, 57864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2015918121, 1999141933, 1932034093, 1848149037, 1764263985, 1697156145], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1646825521, 1562940469, 1512609845, 1462279221, 1395171385, 1344840761], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311287353, 1244179517, 1210626109, 1177072701, 1126742081, 1093188673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059635265, 1009304645, 975751237, 958975045, 908644425, 891868233], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [858314825, 824761421, 807985229, 1100488696083, 1100505472279, 1100522248475], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100488693027, 1100471914791, 1100152491311, 1100169267507, 1100186043707, 1100202819907], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100202818891, 1100219595091, 1100253148507, 1100219593059, 674999657, 4919634293], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4886078845, 9130713481, 9080380821, 13325015457, 389191085, 4617048509], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4566715849, 1099783982539, 1099750427091, 8794573273, 1099700094431, 8727463401], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099649761771, 1099616206323, 12938543613, 1099565873663, 1099549237759, 1099532459527], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1864926253, 1781041201, 1713933361, 1646825521, 1579717685, 1529387061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1479056437, 1411948601, 1361617977, 1311287353, 1260956733, 1210626109], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1177072701, 1126742081, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [942197829, 908644425, 875091017, 858314825, 807984205, 791208013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100505473295, 1100522249491, 1100522248475, 1100505470239, 1100471914791, 1100169268523], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100169267507, 1100186043707, 1100202819907, 1100202818891, 1100236372307, 1100253148507], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100219593059, 658222445, 4919634293, 4869301633, 9113936269, 9063603609], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13308238245, 372413873, 4617048509, 1099783982539, 4549938637, 1099750427091], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8777796061, 1099700094431, 1099649761771, 8710686189, 1099616206323, 1099532460543], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099549096451, 1099532459527, 57860, 57864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1663602737, 1579717685, 1529387061, 1479056437, 1411948601, 1361617977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1311287353, 1260956733, 1210626109, 1177072701, 1126742081, 1093188673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059635265, 1009304645, 975751237, 942197829, 891867209, 875091017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [841537609, 807984205, 774430797, 1100505473291, 1100522249491, 1100539025687], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100505470239, 1100488692003, 1100169268523, 1100169267507, 1100186043707, 1100202819907], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100219596107, 1100236372307, 1100253148507, 1100219593059, 658222445, 4919634293], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4869301633, 9113936269, 9063603609, 13308238245, 372413873, 4600271297], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099783982539, 1099750427091, 1099700094431, 1099649761771, 1099599429111, 1099549237755], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099549096451, 1099532459527, 57860, 57864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1479056437, 1411948601, 1378395193, 1328064569, 1260956733, 1227403325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1177072701, 1126742081, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [942197829, 891867209, 875091017, 841537609, 807984205, 774430797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100505473291, 1100522249491, 1100539025687, 1100505470239, 1100488692003, 1100169268523], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100169267507, 1100186043707, 1100202819907, 1100219596107, 1100236372307, 1100253148507], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [389198181, 4953189741, 4902857081, 9147491717, 9113936269, 9063603609], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099783982539, 1099750427091, 1099700094431, 1099649761771, 1099599429111, 1099549237755], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099549096451, 1099532459527, 57860, 57864], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 130 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 11 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group11
