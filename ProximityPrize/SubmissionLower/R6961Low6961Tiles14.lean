import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [32103664647, 1989618707, 1989685267, 1972909079, 1972975639, 1972976663], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1956266011, 1956267035, 1956333595, 1939557407, 1939558431, 1939559455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1922848803, 1922849827, 1922850851, 1906074663, 1906075687, 1906142247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1889366059, 1889367083, 1889368107, 1872591919, 1872592943, 1872593967], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1855817779, 1855818803, 1855885363, 1839109175, 1839110199, 1839111223], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1822335035, 1822336059, 1822337083, 1721674815, 1721675839, 1721676863], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1704900675, 1738456131, 1738457155, 12962409947, 4338990563], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i43 : checks (tilesOf batches) 122 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40677480459, 1956266011, 1956267035, 1956333595, 1939557407, 1939558431], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1939559455, 1922848803, 1922849827, 1922850851, 1906074663, 1906075687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1906142247, 1839034411, 1839035435, 1839036459, 1822260271, 1822261295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1822262319, 1805486131, 1805487155, 1805553715, 1788777527, 1788778551], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1788779575, 1772003387, 1772004411, 1772005435, 1805560895, 1805561919], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1805562943, 1788786755, 966704195, 966705219, 5110742315, 34403611107], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [21518783971], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i46 : checks (tilesOf batches) 122 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1872045071, 1855268883, 1855400979, 1855467539, 1838691351, 1838757911], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1838758935, 1822048283, 1822049307, 1822115867, 1805339679, 1805340703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1939559455, 1922848803, 1922849827, 1922850851, 1906074663, 1906075687], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1906142247, 1889366059, 1889367083, 1889368107, 1872591919, 1402830895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1402831919, 1386055731, 1386056755, 1386123315, 1369347127, 1369348151], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1369349175, 1822335035, 1822336059, 1822337083, 1805560895, 1805561919], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1805562943, 1788786755, 1704901699, 1285472323, 497009015, 30528143743], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [47372248527, 4372544987], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1989685267, 1972909079, 1972975639, 1972976663, 1956266011, 1956267035], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1956333595, 1939557407, 1939558431, 1939559455, 1922848803, 1922849827], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1906073635, 1889297447, 1889298471, 1889365031, 1872588843, 1872589867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1872590891, 1855814703, 1855815727, 1855816751, 1839040563, 1839041587], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1839108147, 1822331959, 1822332983, 1822334007, 1805557819, 1822336059], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1822337083, 1805560895, 1805561919, 1805562943, 1788786755, 1402911811], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1402912835, 4674534803, 38665019883, 25780193771], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 122 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 122 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 122 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1855536151, 1838825499, 1838826523, 1838893083, 1822116895, 1822117919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1822118943, 1805408291, 1805409315, 1805410339, 1788634151, 1788635175], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1906142247, 1889366059, 1889367083, 1889368107, 1872591919, 1872592943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1872593967, 1855817779, 1855818803, 1855885363, 1805554743, 1805555767], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1805556791, 1788780603, 1788781627, 1788782651, 1805560895, 1755230271], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1755231295, 1738455107, 1738456131, 1537130563, 245350835, 47355542995], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8633889251, 4338990563, 21502006759], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 122 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 122 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 122 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 122 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 122 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1872447515, 1855671327, 1855672351, 1855673375, 1838962723, 1838963747], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1838964771, 1822188583, 1822189607, 1822256167, 1805479979, 1805481003], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1805482027, 1788705839, 1788706863, 1788707887, 1771931699, 1771932723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1771999283, 1755223095, 1755224119, 1839111223, 1772003387, 1772004411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1772005435, 1755229247, 1755230271, 1755231295, 1738455107, 1738456131], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1788788803, 47321991643, 34437233115, 17223819747, 8633955811], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 122 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 122 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 122 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 122 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1805341727, 1788631075, 1788632099, 1788633123, 1771856935, 1771857959], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1771924519, 1755148331, 1755149355, 1755150379, 1738374191, 1738375215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1738376239, 1235060787, 1235061811, 1235128371, 1218352183, 1218353207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1218354231, 1201578043, 1201579067, 1805559867, 1788783679, 1788784703], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1788785727, 1788786755, 1168030787, 1788788803, 30679140699, 4909415771], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [47372391887, 30192600527, 12895300075], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 122 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 122 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 122 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 122 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1922850851, 1906074663, 1906075687, 1906142247, 1889366059, 1889367083], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1889368107, 1872591919, 1872592943, 1872593967, 1855817779, 1855818803], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1688113203, 1335792695, 1335793719, 1335794743, 1319018555, 1319019579], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1319020603, 1302244415, 1805561919, 1805562943, 1788786755, 1788787779], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1285472323, 26266735991, 497009015, 25931190727], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 122 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 122 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 122 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 122 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1688038439, 1671262251, 1671263275, 1671264299, 1654488111, 1654489135], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1654490159, 1637713971, 1637714995, 1637781555, 1621005367, 1839110199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1839111223, 1822335035, 1822336059, 1822337083, 1805560895, 1805561919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1805562943, 1470019651, 1470020675, 1470021699, 8902392227, 43161316795], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1872590891, 1855814703, 1855815727, 1855816751, 1839040563, 1839041587], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1839108147, 1822331959, 1822332983, 1822334007, 1805557819, 1805558843], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1805559867, 1788783679, 1788784703, 1788785727, 1788786755, 1671347267], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1671348291, 4406099411, 38665091563, 21485232619], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1855816751, 1839040563, 1839041587, 1839108147, 1822331959, 1822332983], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1822334007, 1805557819, 1805558843, 1805559867, 1721674815, 1721675839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1721676863, 1704900675, 6083755075, 17257377243, 34370127339, 17190267371], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1839108147, 1822331959, 1822332983, 1822334007, 1805557819, 1805558843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1805559867, 1788783679, 1788784703, 1319023679, 1302247491, 1302248515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1302249539, 13365065083, 30075163115, 17190334955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group14
