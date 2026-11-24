import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass31

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group31
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [15117650949, 10789133325, 2182424593, 2182425617, 2132094993, 1930769429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1779775509, 1645558805, 1528119321, 1427457049, 1343571993, 1259686941], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1192579101, 1142248477, 19297556513, 10690849831, 6379108395, 2067365935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2017035311, 1933150259, 1882819635, 1832489011, 1782158391, 1731827767], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1698274359, 1631166523, 1597613115, 1564059707, 1530506303, 1496952895], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1463399487, 1429846083, 1396292675, 1379516483, 1345963079, 1329186887], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1312410695, 1278857291, 1262081099, 18156705073, 22401339711, 22334229837], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26562087263, 26478200179, 1100187686267, 1100170908031, 1100154129795, 1100137351559], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26377535881, 1100120573323, 1100103795087, 575389075, 541833627, 424392093], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [30571838883, 4786467239, 4752911791, 9031100851, 8997545403, 30437620163], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13258957251, 13208624591, 17470036439, 17419703779, 30286624231, 17386148331], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [21630782967, 21580450307, 30102073873, 25808307731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
private theorem i51 : checks (tilesOf batches) 134 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10805909513, 6494168077, 2182425617, 2132094993, 1930769429, 1762998293], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1628781589, 1511342105, 1410679833, 1326794777, 1226132509, 1159024669], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1091916829, 19297556515, 10690849831, 2084141097, 2067364911, 2017034287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1949926447, 1866041395, 1815710771, 1765380147, 1698272309, 1664718903], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1614388277, 1564057657, 1530504249, 1496950841, 1446620221, 1413066813], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1396290621, 1345960001, 1329183809, 1295630401, 1262076997, 1245300805], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1228524613, 1194971209, 1178195017, 18207036709, 22434894135, 22367784261], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22283897177, 1100271572327, 1100254794091, 26494977391, 1100238015855, 1100221237619], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100204459383, 1100187681147, 1100154125699, 26394313093, 1100137347463, 592164239], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [457945489, 4836797851, 26293648797, 4803242403, 4769686955, 9031098803], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8997543355, 30454397375, 13242177991, 13208622543, 17453257179, 30286624231], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17402924519, 17352591859, 21580449283, 30102073873, 21513339411], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [6494168077, 2182425617, 2148872209, 1947546645, 1779775509, 1645558805], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1511342105, 1410679833, 1310017561, 1209355293, 1142247453, 1075139613], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [19297556515, 6395882533, 2084140073, 2084141097, 2033810479, 1966702639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1899594797, 1832486963, 1765379121, 1715048497, 1647940661, 1614387253], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1564056629, 1513726009, 1480172601, 1446619193, 1396288573, 1362735165], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1345958973, 1295628353, 1278852161, 1245298753, 1211745349, 1194969157], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1178192965, 1127862345, 1111086153, 18223813921, 18156704049, 22384561475], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22300674389, 1100338681175, 1100321902939, 1100288347491, 1100271569255, 1100254791019], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26494977391, 1100238012783, 1100204457335, 1100187679099, 1100154123651, 26394313093], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100137345415, 592162191, 491497877, 4820018591, 26276871585, 4786463143], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [9047874991, 8997542331, 30437620163, 13258954179, 13208621519, 17453256155], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [30269847019, 17386146283, 17335813623, 21563671047, 30085296661, 21496561175], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
private theorem i49 : checks (tilesOf batches) 134 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [2182426641, 1981101077, 1813329941, 1662336021, 1528119321, 1410679833], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1326794777, 1226132509, 1142247453, 1075139613, 19297556515, 6395882533], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2084140073, 2084141097, 2017033261, 1949925423, 1882817581, 1798932529], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1748601905, 1698271281, 1631163445, 1580832821, 1547279413, 1480171577], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1446618169, 1413064761, 1362734141, 1329180733, 1312404541, 1262073921], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1228520513, 1211744321, 1161413701, 1144637509, 1127861317, 1094307913], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1077531721, 18223813921, 18156704049, 22367784263, 1100372235599, 1100355457363], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100338679127, 22283897177, 1100321900891, 1100305122655, 1100271567207, 1100254788971], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [26494977391, 1100221233523, 1100187678075, 1100170899839, 1100137344391, 26377535881], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [592161167, 508274069, 4820017567, 26260094373, 4769684907, 9031096755], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8980764095, 30404065739, 13225398731, 13175066071, 17419700707, 30236292595], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17352590835, 17285480963, 21513338387], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
private theorem i52 : checks (tilesOf batches) 134 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1679113237, 1544896537, 1427457049, 1326794777, 1226132509, 1159024669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1091916829, 19297556515, 6395882533, 2084140073, 2084141097, 2017033261], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1933148205, 1866040365, 1798932529, 1731824689, 1681494065, 1614386229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1564055605, 1530502197, 1463394361, 1429840953, 1396287545, 1345956925], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1312403517, 1278850109, 1228519489, 1194966081, 1178189889, 1127859269], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1111083077, 1094306885, 1060753481, 1027200073, 18207036709, 18139926837], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100422567235, 22367784261, 1100389011787, 1100372233551, 1100355455315, 1100338677079], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22283897177, 1100305121631, 1100288343395, 1100254787947, 26478200179, 1100221232499], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100187677051, 1100154121603, 608938379, 26360758669, 508274065, 4836794779], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4786462119, 26243317161, 9047873967, 8997541307, 13242175943, 13191843283], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13124733411, 17369368047, 17302258175, 21513338387], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1360349209, 1242909725, 1175801885, 1091916829, 19297556515, 6395882533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2084140073, 2084141097, 2017033261, 1949925421, 1882817581, 1798932529], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1731824689, 1681494065, 1614386229, 1564055605, 1513724981, 1463394361], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1413063737, 1379510329, 1329179709, 1295626301, 1262072893, 1211742273], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1178188865, 1144635457, 1111082053, 1077528645, 1060752453, 1027199049], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [993645641, 18207036709, 18123149625, 1100456121659, 1100422566211, 1100405787975], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22351007049, 1100389009739, 1100355454291, 1100338676055, 1100305120607, 22250342753], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100271565159, 1100238009711, 1100204454263, 1100170898815, 1100137343367, 592160143], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [525050265, 4803239331, 4752906671, 8997541307, 8947208647, 13191843283], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13124733411, 17352590835, 17285480963, 21513338387], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1108694045, 19297556513, 6395882533, 2084140073, 2084141097, 2033810477], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1949925421, 1882817581, 1798932529, 1748601905, 1681494065, 1614386229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1564055605, 1513724981, 1446617145, 1413063737, 1362733113, 1312402493], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1278849085, 1245295677, 1194965057, 1161411649, 1127858241, 1094304837], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1060751429, 1043975237, 993644617, 976868425, 18190259497, 1100472898871], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100456120635, 1100422565187, 1100405786951, 1100372231503, 1100355453267, 1100321897819], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100288342371, 1100254786923, 1100221231475, 1100187676027, 1100154120579, 592160143], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [541827477, 4803239331, 4752906671, 8997541307, 8947208647, 13175066071], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13124733411, 17352590835, 17285480963, 21496561175], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [15002591265, 6379106345, 2084141097, 2050587693, 1966702637, 1899594797], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1815709745, 1748601905, 1698271281, 1614386229, 1564055605, 1513724981], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1446617145, 1413063737, 1362733113, 1312402493, 1262071869, 1228518461], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1178187841, 1144634433, 1127858241, 1077527621, 1043974213, 1027198021], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [976867401, 960091209, 1100489676083, 1100472897847, 1100439342399, 1100422564163], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100389008715, 1100355453267, 1100338675031, 1100305119583, 1100271564135, 1100238008687], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100187676027, 1100154120579, 592160143, 541827477, 4803239331, 4752906671], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8997541307, 8930431435, 13175066071, 13107956199, 17335813623, 17268703751], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [21479783963], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10690849829, 2084141097, 2067364909, 1983479853, 1916372013, 1832486961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765379121, 1698271281, 1631163445, 1564055605, 1513724981, 1463394361], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1413063737, 1362733113, 1312402493, 1262071869, 1228518461, 1178187841], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1144634433, 1111081025, 1060750405, 1043974213, 1010420805, 960090185], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [943313993, 1100506453295, 1100489675059, 1100456119611, 1100422564163, 1100405785927], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100372230479, 1100338675031, 1100305119583, 1100271564135, 1100238008687, 1100187676027], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100154120579, 592160143, 541827481, 4803239331, 4752906669, 8980764095], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8930431433, 13158288859, 13091178987, 17319036411, 17251926539], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2084141097, 2067364909, 2000257069, 1933149229, 1849264177, 1782156337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1715048497, 1631163445, 1580832821, 1530502197, 1463394361, 1413063737], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1362733113, 1312402493, 1278849085, 1228518461, 1178187841, 1144634433], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1111081025, 1060750405, 1027196997, 1010420805, 960090185, 926536777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100523230507, 1100489675059, 1100456119611, 1100439341375, 1100405785927, 1100372230479], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100338675031, 1100305119583, 1100271564135, 1100221231475, 1100187676027, 1100154120579], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [592160143, 541827481, 4786462119, 4736129457, 8980764095, 8913654221], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13141511647, 13074401773, 17302259199, 17235149325], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1949926445, 1866041393, 1798933553, 1731825713, 1647940661, 1597610037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1547279413, 1480171577, 1429840953, 1379510329, 1312402493, 1278849085], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1228518461, 1178187841, 1144634433, 1111081025, 1060750405, 1027196997], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [993643589, 960090185, 926536777, 1100523230507, 1100489675059, 1100472896823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100439341375, 1100405785927, 1100372230479, 1100338675031, 1100305119583, 1100271564135], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100221231475, 1100187676027, 1100137343367, 541828497, 4820017567, 4769684907], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9014319543, 8963986883, 13191844307, 13124734435, 17352591859, 17285481987], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1748602929, 1664717877, 1597610037, 1547279413, 1480171577, 1429840953], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1379510329, 1329179709, 1278849085, 1245295677, 1178187841, 1144634433], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1111081025, 1060750405, 1027196997, 993643589, 960090185, 926536777], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100523230507, 1100489675059, 1100472896823, 1100439341375, 1100405785927, 1100372230479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100338675031, 1100305119583, 1100254786923, 1100221231475, 1100170898815, 625715591], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [541828497, 4820017567, 4769684907, 9014319543, 8947209671, 13175067095], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 31 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
end Low6960Allocation.Group31
