import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass7

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23508093959, 36361413647, 1901676571, 1884900383, 1884901407, 1885033503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868257315, 1868323875, 1868324899, 1851614247, 1851615271, 1851616295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1784508459, 1784575019, 1784576043, 1767799855, 1767800879, 1767867439], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1751091251, 1834978355, 1834979379, 1818268727, 1818269751, 1818270775], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1767940155, 1767941179, 1801496635, 1784720447, 1751167039, 1751233599], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1633794115, 1650572355, 1633796163, 1482802247, 1099786536363, 1099652315595], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [6472136, 1099635539407, 1099635540431, 25860010455, 38694504931, 4334920163], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [40022499, 1099551651299, 12891295211, 8596332011, 6400491, 6467051], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i3 : checks (tilesOf batches) 122 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 122 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 122 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32082630667, 1666594839, 1666661399, 1649885211, 1649886235, 1650018331], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1633242143, 1633243167, 1633375263, 1616599075, 1616665635, 1918656547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1901945895, 1901946919, 1901947943, 1885171755, 1885238315, 1885239339], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1868463151, 1801355311, 1801421871, 1784645683, 1784646707, 1784647731], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1818268727, 1818269751, 1818270775, 1818271803, 1784718395, 1784719419], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1734388799, 1583394879, 1583461439, 1466021955, 1466022979, 1466024003], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1449247815, 1099820087715, 1099820088739, 1099820089763, 1099820090787, 38946093479], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099719356859, 1099719423419, 17236591071, 1099568426463, 23176679, 23177703], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8596329963], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i6 : checks (tilesOf batches) 122 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 122 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 122 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2001675279, 1984899091, 1984900115, 1985228819, 1968452631, 1968584727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1968651287, 1951875099, 1951876123, 1129924635, 1113148447, 1113149471], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1113281567, 1096505379, 1096571939, 1096572963, 1079862311, 1079863335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1901947943, 1885171755, 1885238315, 1885239339, 1868463151, 1868464175], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1868530735, 1667205171, 1667206195, 1667207219, 1650496567, 1784715319], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1784716343, 1767940155, 1700832315, 1700833339, 1650502719, 1650503743], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1449243711, 962705475, 962706499, 962707523, 945931335, 35171158315], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [13310736683, 1099887196563, 1099887197587, 1099887198611, 1099887199635, 1099853575579], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13059066307, 1099652246987, 1099652313547, 107062739, 1099618691539, 4334918115], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [39952867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i9 : checks (tilesOf batches) 122 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 122 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 122 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 122 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1834233875, 1817457687, 1817589783, 1817656343, 1800880155, 1800881179], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1801013275, 1784237087, 1784238111, 1784370207, 1012619299, 1012685859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1012686883, 995976231, 995977255, 995978279, 979202091, 979268651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1700689963, 1683913775, 1683914799, 1683981359, 1667205171, 1818201139], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1818202163, 1801491511, 1818269751, 1818270775, 1751162939, 1751163963], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1667278907, 1650502719, 1616949311, 1398912063, 1382135875, 1382136899], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1449246787, 1432470599, 30960146711, 1099903907215, 1099903973775, 1099903974799], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099836866975, 1099836867999, 17353963971, 1099685867971, 38795096523, 1099652245963], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099652246987, 56730079, 1099568358879, 8613105127, 4301363691], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 122 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 122 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 122 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1817656343, 1800880155, 1800881179, 1801013275, 1784237087, 1784238111], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1784370207, 1767594019, 1767660579, 1767661603, 1784505383, 1784506407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1784507431, 1767731243, 1767797803, 1767798827, 1751022639, 1868464175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1583318063, 1566541875, 1566542899, 1566543923, 1801491511, 1801492535], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1801493559, 1650499643, 1650500667, 1650501691, 1314958399, 1314959423], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1315025983, 1298249795, 1197587523, 1197588547, 1180812359, 1100088524131], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100088525155, 1100088526179, 8764108155, 1099987794299, 1099803241895, 1099803242919], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099803309479, 13159663019, 157393351, 1099669022151, 1099669023175, 38795099595], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [25876784595, 4318139879, 23174631], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 122 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 122 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 122 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 122 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 122 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1599686683, 1582910495, 1582911519, 1583043615, 1566267427, 1566333987], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1566335011, 1549624359, 1549625383, 1885170727, 1868394539, 1868461099], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1868462123, 1851685935, 1851686959, 1851753519, 1834977331, 1834978355], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1834979379, 1835045943, 1684052023, 1684053047, 1667276859, 1684055099], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1684056123, 1482730559, 1482731583, 1415689279, 1398913091, 1398914115], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1298251843, 1281475655, 1099987861883, 1099987862907, 1099887130003, 1099887196563], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099887197587, 34701461915, 1099820019107, 1099820020131, 4435581387, 140616139], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099635467727, 1099635468751, 21481156075, 12891293163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 122 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 122 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 122 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 122 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1918587935, 1901811747, 1901878307, 1901879331, 1885168679, 1885169703], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1885170727, 1868394539, 1868461099, 1851684907, 1834908719, 1834909743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [69564597295, 1100491031803, 1100491032827, 1100491033851, 1100222599419, 1100222600443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100222601467, 1100491037947, 1100491104507, 1100340110587, 1100340111611, 1100071677179], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100071678203, 1100071679227, 1100021348603, 1100021349627, 1100021350651, 1100021351675], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100004571511, 1100004638071, 1100004639095, 1100004640119, 1099954236803, 1099954237827], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099954238851, 8881541543, 1099685799363, 1099685800387, 17202969063, 8613105127], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [23174631, 23175655, 34365986283], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 122 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 122 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 122 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 122 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1901879331, 1885168679, 1885169703, 1885170727, 1868394539, 1868461099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868462123, 1851685935, 1851686959, 1851753519, 1834977331, 1834978355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1834979379, 1801491511, 1801492535, 1801493559, 1734385723, 1684055099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1684056123, 1566616639, 1566617663, 1315025983, 1298249795, 1298250819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [945930307, 929154119, 1100340117799, 1100340184359, 1099987793275, 1099987794299], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099987860859, 1099736133047, 1099736134071, 1099635467727, 1099635468751, 73507291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4318139879, 23174631, 30071087595, 17186259435], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 122 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 122 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 122 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 122 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1901947943, 1885171755, 1885238315, 1885239339, 1868463151, 1868464175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868530735, 1633650739, 1633651763, 1633652787, 1616942135, 1767938103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1767939127, 1751162939, 1751163963, 1633724475, 1616948287, 1432399935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1398912063, 1382135875, 1382136899, 1046593603, 1029817415, 1100239520063], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100239521087, 1099903907215, 1099903973775, 1099903974799, 1099870351767, 13092620731], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099685800387, 1099685801411, 4351695327, 56730079, 1099568358879], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1868462123, 1851685935, 1851686959, 1851753519, 1834977331, 1834978355], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1650430003, 1633719351, 1633720375, 1835047991, 1818271803, 1767941179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1700833339, 895527999, 895529023, 18411009087, 17656030487, 1100071680359], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100071746919, 1100071747943, 1100071748967, 1099920682379, 1099920683403, 1099920684427], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8780878271, 1099618691539, 1099551581667, 21481159147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1851753519, 1834977331, 1834978355, 1834979379, 1818268727, 1784715319], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1784716343, 1767940155, 1667277883, 1667278907, 1482730559, 1482731583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482798143, 1247918147, 1298250819, 1298251843, 1281475655, 1100038125935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099987860859, 1099987861883, 1099987862907, 1099820019107, 1099820020131, 1099820086691], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [140617163, 1099652245963, 4334918115, 39952867, 17186260459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 122 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56730030131, 912298251, 912299275, 912300299, 1100423929099, 1100423995659], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100423996683, 1100205893899, 1100205894923, 1100205895947, 1099937461515, 1099937462539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099937463563, 1100021350667, 1100021351691, 1100021347699, 1100021348723, 1100021415283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937530247, 1099937531271, 1099752909235, 1099752910259, 1099752911283, 8613106151], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4318141927, 23176679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤122) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group7
