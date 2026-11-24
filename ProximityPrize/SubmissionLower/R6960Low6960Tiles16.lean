import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass16

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2248215557, 1996623883, 10822095881, 15100747789, 6494040081, 2182297621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2148744213, 1980973081, 1863533593, 1762871321, 27920124957, 15001675813], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6394968105, 2083225645, 2083226669, 2049673265, 1999342641, 1949012017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1881904181, 1831573557, 1798020149, 1747689529, 1697358905, 1663805497], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1613474877, 1596698685, 1563145277, 1512814657, 1496038465, 1462485057], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1428931653, 1412155461, 1395379269, 1361825865, 1328272457, 1311496265], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1294720077, 1100153018759, 1100153019783, 1100136240523, 1100102685075, 1100085906839], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100069128603, 1100052350367, 1100035572131, 490388905, 473610669, 4735022517], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4701467069, 26158516673, 4684688833, 8946100681, 8912545233, 26057852377], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13157179869, 13123624421, 13104058857, 17385036269, 25940410869, 17334703609], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17284370949, 21529005585, 30084382233, 21478672925], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15117522953, 10789005329, 2182296597, 2182297621, 2131966997, 1964195865], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1829979161, 1729316889, 23625157661, 15001674789, 6394967081, 2083224621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2083225645, 2066449453, 1999341617, 1949010993, 1898680369, 1831572533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1781241909, 1730911285, 1680580665, 1647027257, 1613473849, 1563143229], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1529589821, 1496036413, 1462483009, 1428929601, 1412153409, 1361822789], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1345046597, 1328270405, 1277939785, 1261163593, 1244387401, 1210833997], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100236905843, 1100220127607, 1100203349371, 1100186571135, 1100153015687, 1100136237451], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100119459215, 1100085903767, 1100069125531, 1100035570083, 507164069, 473608621], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4735020469, 26192071097, 4701465021, 8962876869, 8929321421, 26091406801], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13190733269, 13140400609, 13090067949, 25957188081, 17334702585, 17284369925], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [21529004561, 30101159445, 21478671901], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [10805781517, 6494040081, 2182297621, 2131966997, 1964195865, 1829979161], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1712539673, 23625157661, 15001674789, 6394967081, 2083224621, 2083225645], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2032895021, 1965787185, 1898679345, 1848348721, 1781240885, 1730910261], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1697356853, 1630249017, 1596695609, 1563142201, 1512811581, 1479258173], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1445704765, 1395374145, 1378597953, 1345044545, 1311491141, 1277937733], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1261161541, 1227608137, 1210831945, 1194055753, 1160502349, 1100287237479], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100270459243, 1100253681007, 1100236902771, 1100220124535, 1100203346299, 1100169790851], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100153012615, 1100119457167, 1100102678931, 1100069123483, 523940257, 490384809], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4751796657, 26208848309, 4718241209, 8979653057, 8929320397, 26091406801], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13190732245, 13140399585, 13090066925, 25957188081, 17334701561, 17267591689], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [25806192149, 21512226325], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [6494040081, 2182297621, 2148744213, 1980973081, 1846756377, 1729316889], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23625157661, 15001674789, 6394967081, 2083224621, 2083225645, 2016117805], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1932232753, 1881902129, 1814794289, 1747686453, 1714133045, 1663802421], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1596694585, 1563141177, 1529587769, 1462479933, 1428926525, 1412150333], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1361819713, 1328266305, 1311490113, 1261159493, 1244383301, 1210829893], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1177276489, 1160500297, 1143724105, 1093393485, 1100354346327, 1100320790879], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100304012643, 1100287234407, 1100270456171, 1100236900723, 1100220122487, 1100186567039], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169788803, 1100136233355, 1100102677907, 1100085899671, 540716445, 490383785], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4751795633, 26192071097, 4718240185, 8962874821, 8912542161, 26074629589], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13173954009, 13123621349, 25940410869, 17351478773, 17301146113, 17234036241], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [25789414937], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2182298645, 1997750297, 1863533593, 1729316889, 23625157661, 15001674789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6394967081, 2083224621, 2083225645, 1999340589, 1915455537, 1865124913], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1798017073, 1730909237, 1680578613, 1630247989, 1579917369, 1529586745], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1496033337, 1445702717, 1412149309, 1378595901, 1328265281, 1294711873], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1261158465, 1227605061, 1194051653, 1177275461, 1126944841, 1110168649], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1093392457, 1059839053, 1100354346319, 1100371122515, 1100354344279, 1100337566043], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100304010595, 1100287232359, 1100253676911, 1100236898675, 1100203343227, 1100169787779], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100136232331, 1100102676883, 557493657, 523938209, 4785350057, 4735017397], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26192071097, 8996429245, 8946096585, 8895763925, 26057852377, 13140398561], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13073288689, 25923633657, 17317923325, 17250813453, 1099532459547], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1746094105, 23625157661, 15001674789, 6394967081, 2083224621, 2066448429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1999340589, 1915455537, 1848347697, 1798017073, 1730909237, 1663801397], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1630247989, 1563140153, 1512809529, 1479256121, 1412148285, 1378594877], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1345041469, 1294710849, 1261157441, 1244381249, 1194050629, 1160497221], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143721029, 1093390409, 1076614217, 1059838025, 1026284621, 1100354346311], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371122507, 1100387898703, 1100371120467, 1100337565019, 1100320786783, 1100287231335], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253675887, 1100236897651, 1100203342203, 1100169786755, 1100136231307, 591048081], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [540715421, 507159973, 4751794609, 26175293885, 4701461949, 8962873797], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8895763925, 13140398561, 13090065901, 17317923325, 17250813453, 1099566013971], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532458523, 21478670877], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [23625159709, 10706709541, 6394968105, 2083225645, 1999340589, 1915455537], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1848347697, 1798017073, 1714132021, 1663801397, 1613470773, 1546362937], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1496032313, 1462478905, 1412148285, 1361817661, 1328264253, 1277933633], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244380225, 1210826817, 1177273413, 1143720005, 1110166597, 1076613193], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1043059785, 1026283593, 992730189, 1100354346303, 1100371122499, 1100404675911], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100387897679, 1100371119443, 1100337563995, 1100304008547, 1100287230311, 1100253674863], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100220119415, 1100186563967, 1100153008519, 1100102675859, 557492633, 523937185], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4768571821, 4718239161, 8962873797, 8912541137, 13140398561, 13090065901], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17317923325, 1099599568395, 17250813453, 1099566012947, 4052508], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15018450977, 10689933353, 2083224621, 2083225645, 2016117805, 1932232753], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1865124913, 1798017073, 1714132021, 1663801397, 1613470773, 1546362937], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1496032313, 1462478905, 1395371069, 1361817661, 1311487037, 1261156417], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1227603009, 1194049601, 1160496197, 1126942789, 1093389381, 1059835977], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026282569, 1009506377, 959175757, 1100354346295, 1100371122495, 1100387898691], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404674891, 1100387896655, 1100354341207, 1100320785759, 1100304007523, 1100270452075], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100236896627, 1100203341179, 1100153008519, 1100119453071, 557492633, 523937185], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4768571821, 4718239161, 8962873797, 8912541137, 13140398561, 13073288689], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17301146113, 1099633122819, 1099582790159, 17234036241, 1099549234711], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10706709541, 6394968105, 2083225645, 2032895021, 1932232753, 1865124913], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1798017073, 1730909237, 1663801397, 1613470773, 1546362937, 1496032313], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1445701689, 1395371069, 1345040445, 1311487037, 1261156417, 1227603009], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1194049601, 1143718981, 1110165573, 1076612165, 1043058761, 1009505353], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [992729161, 942398541, 1100354346291, 1100371122491, 1100404675903, 1100404674887], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100404673867, 1100371118419, 1100337562971, 1100304007523, 1100270452075, 1100236896627], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100203341179, 1100169785731, 1100119453071, 574269845, 523937185, 4768571821], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4718239161, 8962873797, 8895763925, 13140398561, 13073288689, 1099633122815], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17301146113, 1099599567371, 17217259029, 1099549234711, 4051484, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [6394968105, 2083225645, 2032895021, 1949009969, 1881902129, 1814794289], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1730909237, 1680578613, 1613470773, 1546362937, 1496032313, 1462478905], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1395371069, 1345040445, 1311487037, 1261156417, 1210825793, 1177272385], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1126941765, 1110165573, 1076612165, 1026281545, 992728137, 975951945], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [925621325, 1100371123503, 1100371122487, 1100404675899, 1100421452099, 1100404673867], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100371118419, 1100354340183, 1100320784735, 1100287229287, 1100236896627, 1100203341179], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100169785731, 1100119453071, 557492633, 523937185, 4768571821, 4718239161], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8946096585, 8895763925, 13123621349, 13056511477, 1099633122815, 17284368901], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099616344583, 1099566011923, 17217259029, 4051484, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [2049672237, 1965787185, 1898679345, 1831571505, 1747686453, 1680578613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1630247989, 1563140153, 1512809529, 1462478905, 1395371069, 1361817661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311487037, 1261156417, 1210825793, 1177272385, 1126941765, 1093388357], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1059834949, 1026281545, 992728137, 959174729, 925621325, 1100354346287], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100387899699, 1100404675899, 1100421452099, 1100421451079, 1100387895631, 1100354340183], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320784735, 1100287229287, 1100236896627, 1100203341179, 1100153008519, 607825293], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [557492633, 4802127269, 4751794609, 8996429245, 8946096585, 8878986713], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13106844137, 13039734265, 1099633122811, 1099616344583, 17267591689, 1099566011923], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17200481817, 56856, 4051484, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1831571505, 1747686453, 1697355829, 1630247989, 1563140153, 1512809529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1462478905, 1395371069, 1361817661, 1311487037, 1261156417, 1227603009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1177272385, 1126941765, 1093388357, 1059834949, 1009504329, 992728137], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [959174729, 908844109, 1100371123499, 1100387899699, 1100404675899, 1100438229311], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100421451079, 1100387895631, 1100354340183, 1100320784735, 1100270452075, 1100236896627], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100203341179, 1100153008519, 607825293, 557492633, 4802127269, 4751794609], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8996429245, 8929319373, 13173954009, 13106844137, 1099633122811, 1099616344583], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099566011923, 56856, 4051484, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1647025205, 1579917369, 1529586745, 1479256121, 1412148285, 1361817661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1328264253, 1261156417, 1227603009, 1194049601, 1126941765, 1093388357], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1059834949, 1009504329, 992728137, 959174729, 908844109, 1100371123499], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100387899699, 1100404675899, 1100438229311, 1100421451079, 1100387895631, 1100354340183], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100304007523, 1100270452075, 1100236896627, 1100186563967, 1100153008519, 591048081], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [540715421, 4785350057, 4735017397, 8979652033, 1099633122811, 1099616344583], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099566011923, 56856, 4051484, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group16
