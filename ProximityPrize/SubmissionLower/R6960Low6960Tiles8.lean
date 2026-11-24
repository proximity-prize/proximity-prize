import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass8

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2214661125, 973148169, 2198082569, 1543772169, 15067192333, 6460484625], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2148742165, 2148743189, 2131966997, 1980973081, 1846756377, 1746094105], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1628654621, 1544769565, 1477661725, 19279665185, 10672958501, 2066249769], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2049473581, 2015920173, 1965589549, 1898481713, 1848151089, 1797820465], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1730712629, 1697159221, 1663605813, 1613275193, 1579721785, 1546168377], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1495837757, 1479061565, 1445508157, 1411954753, 1378401345, 1361625153], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1328071749, 1311295557, 1294519365, 1260965961, 1244189769, 1227413577], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1193860173, 1177083981, 14093979893, 1100236906859, 1100220063087, 1100203284851], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100186506615, 1100169728379, 1100152950143, 17803269505, 1100136171907, 1100119393671], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100102615435, 1100085706127, 17736159633, 1100052150679, 523744665, 490189217], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [21947239845, 473410981, 4734822829, 8996365749, 21846575549, 8962679229], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8929123781, 13190535629, 21745911253, 13157045717, 17401680353, 17351347693], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [25906659829, 21595982329, 21545649669, 21495317009, 25772441109], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1577326603, 15067192333, 6460484625, 2148742165, 2148743189, 2115189781], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1947418649, 1829979161, 1712539673, 1595100189, 1511215133, 1427330077], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [14984697889, 10672957477, 2066248745, 2066249769, 2032696365, 1965588525], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1915257901, 1831372849, 1781042225, 1747488817, 1680380981, 1646827573], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1596496949, 1546166329, 1512612921, 1479059513, 1428728893, 1411952701], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1378399293, 1344845889, 1311292481, 1294516289, 1260962885, 1227409477], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1210633285, 1177079881, 1160303689, 1143527497, 1126751309, 1109975117], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100304015707, 1100287170911, 1100287171935, 1100270392675, 1100253614439, 1100236836203], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100220057967, 17853601141, 1100186502519, 1100169724283, 1100152814975, 13490002309], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100119259527, 17769714057, 1100102481291, 1100068925843, 540519829, 21980794269], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [506964381, 4768376229, 4734820781, 21880129973, 8996232629, 8945899969], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8912344521, 21762688465, 13157044693, 17418456541, 17368123881, 25940214253], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17301014009, 21545648645, 25789218321, 21478538773], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [10772227085, 6460485649, 2148743189, 2115189781, 1947418649, 1813201945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1712539673, 1578322973, 1494437917, 1410552861, 14984697889, 10672957477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2066248745, 2066249769, 1999141933, 1932034093, 1881703469, 1797818417], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1747487793, 1697157169, 1630049333, 1596495925, 1562942517, 1495834681], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1462281273, 1428727865, 1378397245, 1361621053, 1328067645, 1277737025], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1260960833, 1244184641, 1193854021, 1177077829, 1160301637, 1126748233], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1109972041, 1093195849, 1059642445, 1042866253, 1100354347339, 1100337503567], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337502547, 1100320724311, 1100303946075, 1100287167839, 1100270389603, 1100253611367], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100220055919, 17870378353, 1100203146611, 1100186368375, 1100152812927, 17786491269], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100119257479, 1100102479243, 557296017, 17702604185, 523740569, 4785152417], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4734819757, 21880129973, 8996231605, 8962676157, 8912343497, 21779465677], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13157043669, 17401678305, 25940214253, 17334568433, 17284235773, 21512093197], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [25789218321, 3857940, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [6460485649, 2148743189, 2131966997, 1964195865, 1829979161, 1712539673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1595100189, 1494437917, 1410552861, 14984697889, 6377990181, 6361215017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2066249769, 1982364717, 1915256877, 1848149037, 1781041201, 1713933361], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1663602737, 1613272117, 1562941493, 1512610869, 1462280249, 1428726841], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1395173433, 1344842813, 1311289405, 1277735997, 1244182593, 1210629185], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1193852993, 1143522373, 1126746181, 1109969989, 1076416585, 1059640393], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1042864201, 1009310797, 992534605, 1100320727359, 1100337503555, 1100354279751], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100371055947, 1100354277711, 1100337499475, 1100320721239, 1100303943003, 1100270387555], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100253478247, 1100219922799, 17870378353, 1100203144563, 1100169589115, 1100136033667], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17786491269, 1100102478219, 557294993, 523739545, 17685826973, 4785151393], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4734818733, 21880129973, 8979453369, 8945897921, 13190532557, 21762688465], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13123488221, 17368122857, 25923437041, 17301012985, 1099532263939, 21528870409], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532262923, 57864, 57868, 1099532261907, 16834064, 25772441109], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [16834068], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2148744213, 1980973081, 1846756377, 1729316889, 1595100189, 1494437917], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1410552861, 14984697889, 6377990181, 6361215017, 2066249769, 1965587501], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1898479661, 1831371821, 1764263985, 1697156145, 1646825521, 1579717685], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1546164277, 1495833653, 1428725817, 1395172409, 1361619001, 1311288381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1277734973, 1244181565, 1210628161, 1177074753, 1143521345, 1109967941], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1093191749, 1059638341, 1026084937, 1009308745, 992532553, 958979149], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [942202957, 1100337504563, 1100354280759, 1100371056955, 1100387833151, 1100404609347], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100387831111, 1100354275663, 1100337497427, 1100320719191, 1100287032671, 1100253477223], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100236698987, 17870378353, 1100203143539, 1100169588091, 1100136032643, 17786491269], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [590849417, 557293969, 17685826973, 4801928605, 4751595945, 9013007793], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [21863352761, 8962675133, 8912342473, 21745911253, 13140265433, 17384900069], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [25906659829, 17317790197, 1099532263931, 1099532262915, 57856, 21545647621], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57860, 1099532261899, 16834056, 16834060, 1099532260883, 33610256], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [33610260], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1746094105, 1611877405, 1511215133, 1427330077, 14984697889, 10672957477], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2066248745, 2066249769, 1965587501, 1898479661, 1831371821, 1747486769], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1697156145, 1646825521, 1579717685, 1529387061, 1479056437, 1411948601], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378395193, 1344841785, 1294511165, 1260957757, 1227404349, 1177073729], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143520321, 1126744129, 1076413509, 1059637317, 1026083909, 992530505], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [975754313, 958978121, 925424717, 908648525, 1100320727339, 1100337503535], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100371056947, 1100387833143, 1100404609339, 1100421385535, 1100387830087, 1100371051851], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337496403, 1100320587095, 1100287031647, 1100253476199, 1100219920751, 17853601141], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100186365303, 1100152809855, 607626629, 17769714057, 574071181, 4818705817], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [21964017057, 4768373157, 4718040497, 21846575549, 8962675133, 8912342473], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13157042645, 17384900069, 1099549041135, 17317790197, 1099549040119, 57848], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57852, 1099532261891, 16834048, 17250680325, 16834052, 1099532260875], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [33610248, 33610252, 1099532259859, 50386448, 50386452], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1444107293, 14984697889, 10672957477, 2066248745, 2066249769, 1982364717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1898479661, 1831371821, 1747486769, 1697156145, 1630048305, 1562940469], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1512609845, 1462279221, 1411948601, 1361617977, 1328064569, 1277733949], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244180541, 1210627133, 1160296513, 1126743105, 1093189697, 1059636293], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026082885, 1009306693, 958976073, 942199881, 925423689, 891870285], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [875094093, 1100337504547, 1100354280743, 1100371056939, 1100387833135, 1100421386547], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100421385531, 1100421384511, 1100387829063, 1100371050827, 1100337364307, 1100303808859], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100270253411, 1100236697963, 1100203142515, 17836823929, 1100169587067, 1100136031619], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [574071181, 540515733, 4785150369, 4734817709, 8979452345, 8912342473], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13157042645, 17384900069, 1099532263915, 1099532262899, 57840, 17317790197], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57844, 1099532261883, 16834040, 16834044, 1099549038083, 33610240], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610244, 17233903113, 33610248, 1099532259855, 50386444, 50386448], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [3853844, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14984699937, 6361215017, 2066249769, 1982364717, 1915256877, 1848149037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764263985, 1697156145, 1630048305, 1562940469, 1512609845, 1462279221], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395171385, 1361617977, 1311287353, 1260956733, 1227403325, 1193849917], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1143519297, 1109965889, 1076412481, 1042859077, 1009305669, 992529477], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942198857, 925422665, 891869257, 858315853, 841539661, 1100337504539], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371057951, 1100387834147, 1100387833131, 1100421386543, 1100421385527, 1100438161723], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100404606275, 1100387828039, 1100354141519, 1100320586071, 1100287030623, 1100253475175], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100219919727, 1100186364279, 1100136031619, 590848393, 540515733, 4785150369], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4734817709, 8979452345, 8912342473, 13140265433, 1099549041123, 17368122857], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532262895, 57836, 57840, 1099532261879, 16834036, 17301012985], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16834040, 1099549038079, 33610236, 33610240, 33610244, 21528870409], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099532259851, 50386440, 50386444, 1099532258835, 67162640, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 133 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6377991205, 2066248745, 2066249769, 1999141933, 1932034093, 1848149037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764263985, 1697156145, 1646825521, 1562940469, 1512609845, 1462279221], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395171385, 1361617977, 1311287353, 1260956733, 1227403325, 1177072701], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1126742081, 1093188673, 1076412481, 1026081861, 992528453, 975752261], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [925421641, 908645449, 875092041, 841538637, 824762445, 1100337504535], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371057947, 1100387834143, 1100387833127, 1100421386539, 1100438162739, 1100454938935], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100421383487, 1100387828039, 1100370918731, 1100337363283, 1100303807835, 1100253475175], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100219919727, 1100186364279, 1100136031619, 590848393, 4835483029, 4785150369], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4734817709, 8962675133, 8912342473, 13140265433, 1099549041119, 17368122857], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532262891, 57832, 57836, 1099532261875, 16834032, 16834036], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099549038075, 33610232, 17284235773, 33610236, 33610240, 1099532259847], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386436, 50386440, 21512093197, 67162636, 1099532258835, 67162640], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2066249769, 2015919149, 1932034093, 1864926253, 1781041201, 1713933361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1646825521, 1579717685, 1529387061, 1479056437, 1411948601, 1361617977], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311287353, 1260956733, 1227403325, 1177072701, 1126742081, 1093188673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059635265, 1009304645, 992528453, 958975045, 908644425, 891868233], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [875092041, 824761421, 807985229, 1100354281747, 1100371057943, 1100371056927], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404610339, 1100421386535, 1100438162735, 1100454938935, 1100438160699, 1100404605251], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100370918731, 1100337363283, 1100303807835, 1100253475175, 1100219919727, 1100186364279], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624403841, 574071181, 4818705817, 4768373157, 9013007793, 8962675133], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13190532557, 13123488221, 1099532263903, 1099532262887, 57828, 57832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17351345645, 1099549039087, 16834028, 16834032, 16834036, 1099532260859], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610232, 17284235773, 33610236, 1099549037059, 50386432, 50386436], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386440, 1099549036047, 67162636, 21495315985, 67162640, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1881703469, 1797818417, 1730710577, 1663602737, 1579717685, 1529387061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1479056437, 1411948601, 1361617977, 1328064569, 1260956733, 1227403325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1177072701, 1126742081, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [958975045, 908644425, 875091017, 858314825, 824761421, 791208013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100354281743, 1100354280727, 1100387834139, 1100404610335, 1100421386535, 1100438162735], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100471716147, 1100438160699, 1100404605251, 1100370918731, 1100337363283, 1100303807835], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253475175, 1100219919727, 1100169587067, 624403841, 574071181, 4818705817], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4768373157, 9013007793, 8945897921, 13173820881, 1099532263899, 13106711009], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099549040099, 57824, 57828, 57832, 1099532261871, 16834028], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17334568433, 16834032, 1099549038071, 33610228, 33610232, 33610236], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099549037059, 50386432, 50386436, 50386440, 1099549036047, 67162636], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162640, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1680379953, 1596494901, 1546164277, 1495833653, 1428725817, 1378395193], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1328064569, 1260956733, 1227403325, 1193849917, 1126742081, 1093188673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059635265, 1009304645, 975751237, 958975045, 908644425, 875091017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [858314825, 807984205, 791208013, 1100354281743, 1100371057939, 1100387834139], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100404610335, 1100421386535, 1100438162735, 1100471716147, 1100438160699, 1100404605251], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100370918731, 1100337363283, 1100287030623, 1100253475175, 1100219919727, 1100169587067], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [607626629, 557293969, 4801928605, 4751595945, 8996230581, 8929120709], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532263899, 1099549040099, 57824, 57828, 57832, 1099532261871], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16834028, 16834032, 1099549038071, 33610228, 33610232, 33610236], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099549037059, 50386432, 50386436, 50386440, 1099549036047, 67162636], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162640, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1495833653, 1428725817, 1378395193, 1328064569, 1277733949, 1227403325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1193849917, 1143519297, 1093188673, 1059635265, 1009304645, 975751237], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [958975045, 908644425, 875091017, 841537609, 807984205, 774430797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100371058955, 1100371057939, 1100404611351, 1100404610335, 1100421386535, 1100438162735], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100471716147, 1100438160699, 1100404605251, 1100370918731, 1100320586071, 1100287030623], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100253475175, 1100203142515, 1100169587067, 607626629, 557293969, 4801928605], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532263899, 1099549040099, 57824, 57828, 57832, 1099532261871], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [16834028, 16834032, 1099549038071, 33610228, 33610232, 33610236], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099549037059, 50386432, 50386436, 50386440, 1099549036047, 67162636], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [67162640, 67162644], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group8
