import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass19

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group19
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 2214858761, 10805384201, 6493642765, 2181900305, 2030906385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1846358033, 2064659477, 1896888341, 1762671637, 1628454937, 1527792665], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1443907609, 1343245341, 1276137501, 1225806877, 1141921825, 1108368417], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1058037793, 1007707173, 974153765, 940600357, 890269737, 856716329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [839940137, 6361414701, 2066449453, 2016118833, 1949010993, 1898680369], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1848349749, 1798019125, 1764465717, 1714135097, 1663804473, 1630251065], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1596697661, 1563144253, 1529590845, 1496037441, 1462484033, 1445707841], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1412154437, 1378601029, 1361824837, 1328271433, 1311495241, 1294719049], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1261165645, 5522553077, 9800742137, 9767186689, 9733631241, 13995043089], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13961487641, 18222899489, 18172566829, 18139011381, 22366868805, 22316536145], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [22249426273, 26460506485, 1100169862527, 1100153084291, 1100136306055, 26376619401], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100119527819, 1100102749583, 1100085971347, 1100052415899, 1100035637663, 26275955105], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [507231649, 3914152, 4751865261, 4718309813, 30453480893, 8979721661], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8962943425, 8929387977, 30386368973, 13174022613, 13140467165, 17401879013], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17351546353, 135278073, 17317990905, 21562625541, 21495515669], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10805385225, 2198676493, 2181900305, 2030906385, 1829580817, 2047882261], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1880111125, 1745894421, 1611677721, 1494238233, 1410353177, 1309690909], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1242583069, 1175475229, 1108367393, 1058036769, 1007706145, 940598309], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [907044901, 873491493, 823160873, 806384681, 772831273, 2066447405], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2066448429, 2032895021, 1965787185, 1898679345, 1848348721, 1798018101], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1747687477, 1697356853, 1647026233, 1613472825, 1579919417, 1529588797], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1496035389, 1462481981, 1428928577, 1395375169, 1378598977, 1345045573], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1311492165, 1294715973, 1261162569, 1244386377, 1227610185, 1194056781], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [5589661925, 5556106477, 9834295537, 9800740089, 9767184641, 14028596489], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13978263829, 18222898465, 18172565805, 18122233145, 22350090569, 22282980697], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [26494060909, 1100236971375, 1100220193139, 1100203414903, 1100186636667, 1100169858431], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26410173825, 1100153080195, 1100119524747, 1100102746511, 1100085968275, 540785049], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [26292732317, 524006813, 490451365, 4751863213, 4718307765, 26175290809], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8979719613, 8946164165, 30403146185, 13207576013, 13157243353, 13106910693], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17368322541, 135278073, 17317989881, 21545847305, 21495514645], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2198676493, 2181900305, 2047683601, 1846358033, 2064659477, 1896888341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1745894421, 1611677721, 1494238233, 1393575961, 1292913693, 1225805853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1158698013, 1074812961, 1024482337, 974151713, 907043877, 873490469], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [839937061, 789606441, 756053033, 739276841, 2066447405, 2066448429], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1999340589, 1915455537, 1865124913, 1814794289, 1747686453, 1697355829], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1663802421, 1596694585, 1563141177, 1529587769, 1479257149, 1445703741], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1412150333, 1378596929, 1345043521, 1328267329, 1277936709, 1261160517], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1244384325, 1194053705, 1177277513, 1160501321, 1126947917, 2848988], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [5606438113, 5572882665, 9834294513, 9800739065, 14062150913, 14011818253], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18256452889, 18206120229, 18139010357, 22366867781, 22299757909, 1100304080223], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100287301987, 1100270523751, 22215870825, 1100253745515, 1100220190067, 1100203411831], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100186633595, 26410173825, 1100153078147, 1100136299911, 1100102744463, 574338449], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [540783001, 26292732317, 507227553, 4768639401, 4735083953, 26175290809], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8996495801, 8946163141, 30386368973, 13207574989, 13157242329, 13106909669], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [17351544305, 118500861, 17301211645, 21529069069], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1863135249, 2081436693, 1913665557, 1762671637, 1611677721, 1494238233], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1393575961, 1292913693, 1209028637, 1141920797, 1058035745, 1007705121], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [957374497, 890266661, 856713253, 806382629, 756052009, 739275817], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [705722409, 2066447405, 2049671213, 1982563373, 1898678321, 1831570481], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1781239857, 1714132021, 1663801397, 1630247989, 1563140153, 1529586745], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1496033337, 1445702717, 1412149309, 1378595901, 1328265281, 1294711873], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1277935681, 1227605061, 1210828869, 1194052677, 1143722057, 1126945865], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1110169673, 1076616269, 1361803477, 5623215325, 5606437089, 9867848937], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9817516277, 14078928125, 14028595465, 18273230101, 18222897441, 18155787569], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22383644993, 1100354411859, 22299757909, 1100337633623, 1100320855387, 1100304077151], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100270521703, 22215870825, 1100253743467, 1100236965231, 1100203409783, 1100186631547], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26410173825, 1100153076099, 1100119520651, 574337425, 540781977, 26292732317], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4802193825, 4768638377, 4735082929, 26158513597, 8979717565, 8946162117], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [30369591761, 13190796753, 13140464093, 17385098729, 17317988857, 17250878985], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [21478736409], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1779448853, 1628454937, 1511015449, 1410353177, 1309690909, 1225805853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1141920797, 1058035745, 1007705121, 957374497, 890266661, 839936037], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [806382629, 756052009, 722498601, 688945193, 2066447405, 2032893997], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1965786157, 1881901105, 1831570481, 1764462641, 1697354805, 1647024181], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1596693557, 1546362937, 1496032313, 1462478905, 1412148285, 1378594877], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1345041469, 1294710849, 1261157441, 1244381249, 1194050629, 1177274437], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1143721029, 1110167625, 1093391433, 1076615241, 1026284621, 1378580689], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [5639992537, 5606437089, 9867848937, 9834293489, 14078928125, 14028595465], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18273230101, 18222897441, 18155787569, 22366867781, 1100387966279, 1100371188047], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100354409811, 1100337631575, 22282980697, 1100320853339, 1100287297891, 1100270519655], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [22199093613, 1100236964207, 1100220185971, 1100186630523, 1100153075075, 26393396613], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100119519627, 574336401, 540780953, 26275955105, 4802192801, 4751860141], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [9013271989, 26141736385, 8962939329, 13207573965, 13157241305, 13090131433], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [17334766069, 17267656197, 21495513621, 4120088], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1427130393, 1309690909, 1225805853, 1158698013, 1074812961, 1007705121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [957374497, 890266661, 839936037, 806382629, 739274793, 705721385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [672167977, 2066447405, 2032893997, 1965786157, 1881901105, 1814793265], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1764462641, 1680577589, 1630246965, 1579916341, 1529585721, 1479255097], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1445701689, 1395371069, 1345040445, 1311487037, 1261156417, 1244380225], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1210826817, 1160496197, 1143720005, 1110166597, 1076613193, 1059837001], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1026283593, 992730189, 1395357901, 5656769749, 5623214301, 9867848937], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9834293489, 14078928125, 14028595465, 18273230101, 18206120229, 18139010357], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100387966271, 1100421519683, 22366867781, 1100387964235, 1100371185999, 1100354407763], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22282980697, 1100320852315, 1100304074079, 1100270518631, 1100236963183, 26477283697], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100220184947, 1100186629499, 1100153074051, 591113613, 557558165, 4818970013], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4768637353, 9030049201, 8979716541, 8929383881, 13157241305, 13106908645], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [17334766069, 17267656197, 1099549302291, 21495513621], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1175475229, 1091590177, 1024482337, 957374497, 890266661, 839936037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [806382629, 739274793, 705721385, 672167977, 2066447405, 2032893997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1965786157, 1881901105, 1814793265, 1764462641, 1680577589, 1630246965], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1579916341, 1512808505, 1479255097, 1428924473, 1378593853, 1328263229], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1294709821, 1244379201, 1210825793, 1194049601, 1143718981, 1110165573], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1093389381, 1043058761, 1026282569, 1009506377, 959175757, 1395357901], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [5656769749, 5623214301, 9867848937, 9834293489, 14078928125, 14028595465], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18256452889, 18189343017, 1099732606263, 18122233145, 1100404742463, 1100421518659], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100404740423, 1100371184975, 1100354406739, 1100320851291, 1100287295843, 1100270517607], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100236962159, 1100169862511, 1100203406711, 1100169851263, 607890825, 574335377], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4818970013, 4785414565, 4735081905, 8979716541, 8929383881, 13157241305], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13106908645, 17334766069, 17267656197, 1099566079503, 21495513621, 1099532524055], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [974151713, 907043877, 856713253, 806382629, 756052009, 705721385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [672167977, 2066447405, 2049671213, 1982563373, 1881901105, 1814793265], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1764462641, 1680577589, 1630246965, 1579916341, 1512808505, 1462477881], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1428924473, 1361816637, 1328263229, 1294709821, 1244379201, 1210825793], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1177272385, 1126941765, 1093388357, 1076612165, 1026281545, 1009505353], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [975951945, 942398541, 1395357901, 5656769749, 5606437089, 9867848937], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9817516277, 14062150913, 14011818253, 1099732606259, 1099732605239, 1100421518655], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100421517635, 1100387962187, 1100371183951, 1100337628503, 1100304073055, 1100270517607], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100153085291, 1100236962159, 1100186638703, 1100203406711, 1100169851263, 624668037], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [574335377, 4835747225, 4785414565, 4735081905, 8979716541, 8929383881], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13157241305, 13106908645, 17334766069, 1099599633927, 17250878985, 1099549301267], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [21478736409, 4118040], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [823159845, 756052009, 722498601, 672167977, 2066447405, 2066448429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1982563373, 1898678321, 1831570481, 1764462641, 1697354805, 1630246965], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1579916341, 1512808505, 1462477881, 1428924473, 1361816637, 1328263229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1277932605, 1227601985, 1194048577, 1160495169, 1110164549, 1076611141], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1059834949, 1009504329, 992728137, 959174729, 925621325, 5690325197], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [5639992537, 9901404385, 9851071725, 1099732606255, 1099732605235, 1100421518651], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100438294847, 1100404739399, 1100387961163, 1100354405715, 1100320850267, 1100287294819], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100153085287, 1100253739371, 1100186638699, 1100220183923, 1100169851263, 624668037], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [574335377, 4835747225, 4785414565, 9030049201, 8979716541, 8912606669], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13157241305, 13090131433, 17317988857, 1099616411139, 17250878985, 1099566078479], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099532523031], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [688945193, 2066447405, 2066448429, 1999340589, 1915455537, 1848347697], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1781239857, 1697354805, 1647024181, 1579916341, 1512808505, 1462477881], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1428924473, 1361816637, 1328263229, 1277932605, 1227601985, 1194048577], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160495169, 1110164549, 1076611141, 1043057733, 1009504329, 975950921], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [942397513, 908844109, 5673547985, 1099732606251, 1099732605231, 1099732604215], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100438294847, 1100421516611, 1100387961163, 1100354405715, 1100320850267, 1100287294819], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100153085283, 1100186638695, 1100253739371, 1100203414895, 1100220183923, 1100169851263], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [624668037, 574335377, 4835747225, 4785414565, 9030049201, 8962939329], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13207573965, 13140464093, 13073354221, 17301211645, 1099633188351, 1099582855691], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17234101773, 1099532523031], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [2016117805, 1915455537, 1848347697, 1781239857, 1714132021, 1647024181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1596693557, 1529585721, 1479255097, 1428924473, 1361816637, 1328263229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1277932605, 1227601985, 1194048577, 1160495169, 1110164549, 1076611141], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1043057733, 992727113, 959173705, 942397513, 892066893, 1099732606247], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099732605231, 1099749381427, 1100455072059, 1100421516611, 1100387961163, 1100354405715], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320850267, 1100169862495, 1100287294819, 1100186638695, 1100253739371, 1100203414895], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100220183923, 1100169851263, 624668037, 574335377, 4818970013, 4768637353], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [9013271989, 8962939329, 13190796753, 13140464093, 17368321517, 17301211645], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099633188351, 1099582855691, 17217324561, 1099532523031], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1798017073, 1714132021, 1663801397, 1596693557, 1529585721, 1479255097], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1428924473, 1378593853, 1328263229, 1294709821, 1227601985, 1194048577], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1160495169, 1110164549, 1076611141, 1043057733, 992727113, 959173705], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [942397513, 892066893, 1099732606247, 1099715828015, 1099732604211, 1100455072059], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100421516611, 1100387961163, 1100354405715, 1100320850267, 1100169862495, 1100287294819], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100203415907, 1100253739371, 1100203414891, 1100203406711, 1100169851263, 607890825], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [574335377, 4818970013, 4768637353, 9013271989, 8946162117, 13190796753], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13123686881, 1099633188351, 1099582855691, 1099549300243], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1613470773, 1546362937, 1496032313, 1445701689, 1378593853, 1328263229], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1294709821, 1227601985, 1194048577, 1160495169, 1110164549, 1076611141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1043057733, 992727113, 959173705, 925620297, 892066893, 1099715829031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099732605227, 1099732604211, 1100455072059, 1100421516611, 1100387961163, 1100354405715], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100320850267, 1100186639707, 1100287294819, 1100203415907, 1100253739371, 1100203414891], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100203406711, 1100169851263, 607890825, 557558165, 4802192801, 4751860141], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8996494777, 1099633188351, 1099582855691, 1099549300243], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 19 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group19
