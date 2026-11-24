import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [1949699079, 1932922891, 1932923915, 1934104587, 1917328399, 1917329423], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1917854735, 1901209619, 1901210643, 2102734867, 2085958679, 2085959703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2086157335, 2069381147, 2069382171, 2069514267, 2052738079, 1130057759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1130058783, 1113348131, 1113349155, 1113415715, 1096639527, 1096640551], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1096641575, 1079930923, 1079931947, 2002679851, 1985903663, 1985904687], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1985971247, 1969195059, 1969196083, 1969197107, 1952420919, 1952487479], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1952488503, 1935712315, 31681717307, 39566790959, 1099820017087, 1099820018111], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099752910271, 1099752911295, 1099752912319, 1099803244991, 1099803246015, 1099820024255], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34550123995, 8646667771, 6404615, 6405639], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2017990667, 2001214479, 2001215503, 2001740815, 1985095699, 1985096723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1985294355, 1968518167, 1968519191, 1616395287, 1599619099, 1599620123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1599752219, 1582976031, 1583042591, 1583043615, 1566332963, 1566333987], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1566400547, 1985831975, 1985832999, 1985834023, 86928945195, 1100440629539], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100440630563, 1100440631587, 1100440632611, 1100440633635, 1100474189091, 1100474255651], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100474256675, 1100474257699, 1100474258723, 1100474259747, 1100457483555, 1100457484579], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100457485603, 1100474329379, 1100474330403, 1100440776995, 1100440778019, 1100373670179], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100373671203, 1100205900067, 39113735579, 1099769692619, 38761339375, 1099601918451], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099601919475, 30087800323, 23179779, 23180803, 8596332039], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2001740815, 1985095699, 1985096723, 1985294355, 1968518167, 1968519191], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1968716823, 1951940635, 1951941659, 1952073755, 1935297567, 2019250207], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2019251231, 2002540579, 2002541603, 2002608163, 1985831975, 1985832999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1985834023, 1969123371, 1985901611, 1985902635, 1969126447, 1969127471], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1969194031, 1952417843, 1952418867, 1801424947, 1784648759, 1784715319], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1784716343, 1902157883, 1902158907, 1902159931, 1851829311, 1851830335], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1767945279, 1717680195, 1717681219, 1684127811, 1099719360983, 1099685804511], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099685805535, 13042225635, 1099652249063, 43056375279, 56733179, 1099568361979], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34382696963, 4318142979, 23177731, 25776125447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [2085957651, 2069181463, 2069182487, 2069380119, 2052603931, 2052604955], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2052737051, 2035960863, 2036027423, 2036028447, 1985763363, 1985764387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1985830947, 1969054759, 1969055783, 1969056807, 1952346155, 1952347179], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1952348203, 1985903663, 1985904687, 1985971247, 1969195059, 1969196083], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1969197107, 1667208247, 1667274807, 1667275831, 1851826235, 1851827259], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1851828283, 1784720447, 1784721471, 1616950335, 1600239683, 1197587523], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1197588547, 4687248739, 1099803243971, 1099803244995, 1099803246019, 1099803247043], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8864699847, 1099635469803, 1099635470827, 4368474615, 73509367, 34399541759], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [42955780615], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1868053527, 1851277339, 1851278363, 1851410459, 1834634271, 1834700831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1834701855, 1817991203, 1817992227, 1818058787, 2019386407, 2019387431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2019388455, 2002677803, 2002678827, 2002679851, 1985903663, 1985904687], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1902085167, 1784645683, 1784646707, 1784647731, 1767871543, 1935710263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1935711287, 1918935099, 1818272827, 1818273851, 1751166015, 1751167039], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1566618687, 1549908035, 1549909059, 1315029059, 1100088459647, 1099853575607], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099853576631, 1099853577655, 38862142935, 13059000799, 1099669024227, 1099669025251], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [107062767, 1099618691567, 12958336503, 4301363719, 6398471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1801078811, 1784302623, 1784369183, 1784370207, 1767659555, 1767660579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1767727139, 1750950951, 1750951975, 1750952999, 1969123371, 1969124395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1969125419, 1952349231, 1952350255, 1952416815, 1935640627, 1935641651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1667207219, 1650431031, 1650497591, 1650498615, 1633722427, 1851827259], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1851828283, 1767943231, 1482731583, 1482732607, 1466021955, 1315028035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1315029059, 1100088458623, 1100088459647, 1099937460643, 1099937461667, 1099937462691], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8881476035, 4586577347, 38912477643, 1099652247015, 73508343, 1099585137143], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [21497868803, 12908005891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1549489183, 1532778531, 1532779555, 1532846115, 1516069927, 1516070951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1516071975, 1499361323, 1499362347, 2002679851, 1985903663, 1985904687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1985971247, 1969195059, 1969196083, 1767870515, 1751094327, 1751160887], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1818270775, 1801494587, 1801495611, 1767942203, 1751166015, 1449177151], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1415623743, 1398913091, 1398914115, 1516355651, 34852459923, 1100004570515], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100004571539, 1100004572563, 1099971015067, 6406572, 1099870355891, 8780812763], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099669023203, 1099669024227, 4418805227, 123839979], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1482514467, 1465738279, 1465739303, 1465740327, 1449029675, 1449030699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1449031723, 1432255535, 1902018607, 1902085167, 1885308979, 1885310003], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1885311027, 1935643703, 1935710263, 1935711287, 1902157883, 1835050043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1835051067, 1684057151, 1684058175, 1449178175, 1415690307, 1415691331], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1499578435, 30607827335, 1099987794327, 1099987795351, 1099971016091, 6406568], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099887133103, 1099736133075, 1099736134099, 90285555, 1099601914355, 17253302775], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [23175683, 8596329991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1935502375, 1918791723, 1918792747, 1918793771, 1902017583, 1902018607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1902085167, 1885308979, 1885310003, 1885311027, 1868534839, 1952487479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1818270775, 35490144315, 1100172271947, 1100273001803, 1099987790155, 1099987791179], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099903906123, 1099903907147, 1099903908171, 1100306562379, 1100306563403, 1099903906219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099903907243, 1099903908267, 1099820018111, 1099820019135, 4418805227, 25843166711], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12958337527, 23176707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1902016555, 1885240367, 1885241391, 1885307951, 1868531763, 1868532787], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868533811, 1700762679, 1700829239, 1700830263, 1902157883, 1902158907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1767942203, 1751166015, 1516286015, 1516287039, 1231140931, 1231141955], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1231142979, 1100172343659, 1100172344683, 1100172345707, 1099903906219, 1099903907243], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8831145423, 1099669023203, 1099669024227, 21565045235, 8680149491, 23175683], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [23176707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1868530735, 1851754547, 1851755571, 1851756595, 1834980407, 1952487479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1952488503, 1935712315, 1868604475, 1784719419, 1767943231, 1415622719], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1415623743, 1398913091, 1398914115, 1398915139, 1100004569491, 1100004570515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100004571539, 1100004572563, 1100004573587, 1099652245991, 1099652247015, 17286858223], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56731131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1952419891, 1935643703, 1935710263, 1935711287, 1918935099, 1935713339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868605499, 1784720447, 1432399935, 1432400959, 1415690307, 1449245763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482801219, 1099987792279, 1099987793303, 1099987794327, 1099954240927, 6406564], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099903910315, 1099635469803, 1099568359931, 8596263431, 4301364743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group12
