import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass13

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27839302663, 2020616211, 2020617235, 2020749331, 2003973143, 2003974167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2004171799, 1987395611, 1987396635, 1987463195, 1970752543, 1886867487], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1886868511, 1870157859, 1870158883, 1870159907, 1853383719, 1853450279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1853451303, 1836675115, 1836676139, 1836742699, 1819966511, 1819967535], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1819968559, 1803192371, 1803193395, 1870368819, 1853592631, 1853593655], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1853594679, 1853595707, 1836819515, 1836820539, 1836821567, 1786490943], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1769714751, 1702672451, 1685896259, 1685897283, 1099637243351, 1099637244375], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099620465115, 34434798051, 25845003747, 1099570132455, 41726443, 12893000179], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4303136243], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i3 : checks (tilesOf batches) 124 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 124 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 124 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2053642251, 2036866063, 2036867087, 2037326863, 2020616211, 2020617235], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2020749331, 2003973143, 2003974167, 1534409751, 1517633563, 1517634587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1517701147, 1500990495, 1500991519, 1500992543, 1484281891, 1484282915], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1484283939, 1937269799, 1937336359, 1937337383, 1920561195, 1920562219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1920628779, 1903852591, 1903853615, 1786414127, 1769637939, 1769638963], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1769705523, 1752929335, 1870370871, 1870371895, 1719377979, 1719379003], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1820043323, 1786489919, 1652273215, 1652274239, 1635563587, 1534901315], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1534902339, 39115570567, 1099788238259, 1099788239283, 1099687571915, 1099687572939], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099687573963, 4420575703, 17288627675, 1099553353195, 24947183], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i6 : checks (tilesOf batches) 124 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 124 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 124 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2037326863, 2020616211, 2020617235, 2020749331, 2003973143, 2003974167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2004171799, 1987395611, 1987396635, 1987463195, 1266109471, 1266110495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1266111519, 1249400867, 1249401891, 1249402915, 1232626727, 1232693287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1232694311, 1920561195, 1920562219, 1920628779, 1903852591, 1903853615], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1903854639, 1887078451, 1887079475, 1887146035, 1870369847, 1870370871], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1820040247, 1803264059, 1820042299, 1803266107, 1719381055, 1702604863], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1518056511, 1518123075, 1518124099, 1518125123, 35055488335, 1099821790635], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099805014447, 1099805015471, 1099805016495, 8171988, 1099620462043, 1099620463067], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4336688619, 1099553352171, 24946159], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i9 : checks (tilesOf batches) 124 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 124 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 124 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40675454995, 1903712291, 1903713315, 1903714339, 1886938151, 1887004711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1887005735, 1870229547, 1870230571, 1920628779, 1836743727, 1836744751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1836745775, 1819969587, 1819970611, 1820037171, 1803260983, 1803262007], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1870371895, 1836818491, 1836819515, 1786488891, 1719381055, 1669050431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1518056511, 1501345859, 1518124099, 1518125123, 1099821790635, 1099821791659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099805015471, 1099805016495, 8171980, 1099654017491, 8170968, 1099603684831], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17238293991, 8648364519, 1099570129383, 30106343915, 8167923, 8168947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 124 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 124 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 124 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1836399639, 1819623451, 1819624475, 1819691035, 1802980383, 1802981407], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1802982431, 1786271779, 1786272803, 1786273827, 1920492583, 1920559143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1920560167, 1903783979, 1903785003, 1903851563, 1887075375, 1887076399], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1836745775, 1803192371, 1803193395, 1803259955, 1786483767, 1786484791], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1786485815, 1853595707, 1786487867, 1769711675, 1518054463, 1450946623], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1450947647, 1434236995, 1434238019, 1165803587, 1100157337947, 1099888898459], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099888899483, 1099888900507, 1099888901531, 1099821788587, 38813580751, 12960106979], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4370176483, 8169952, 12943328743, 58500583, 1099570129383, 25777825267], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17187963379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 124 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 124 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 124 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1769359387, 1752648735, 1752649759, 1752650783, 1735940131, 1735941155], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1735942179, 1719165991, 1719232551, 1719233575, 1920561195, 1920562219], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1920628779, 1903852591, 1903853615, 1903854639, 1887078451, 1887079475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1887146035, 1870369847, 1870370871, 1803263031, 1786486843, 1820042299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1719380027, 1702603839, 1417392191, 1417393215, 1400682563, 1300020291], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1300021315, 1100023119227, 1100023120251, 1099922452883, 1099922453907, 1099922454931], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [38863980995, 1099637238231, 1099637239255, 4353465831, 8168940, 8168947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 124 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 124 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 124 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 124 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1685541919, 1668831267, 1668832291, 1668833315, 1652057127, 1652123687], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1652124711, 1635348523, 1635349547, 1635416107, 1618639919, 1618640943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1618641967, 1601865779, 1601866803, 1820037171, 1803260983, 1803262007], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1820040247, 1803264059, 1786487867, 1786488891, 1652272191, 1652273215], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1450947647, 1434236995, 1333574723, 1333575747, 1099989564803, 1099989565827], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099888899483, 1099888900507, 34636125619, 21751364019, 1099687570891, 1099687571915], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8648364519, 58500583, 1099570129383, 4336688619], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 124 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 124 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 124 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 124 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1937268771, 1920492583, 1920559143, 1920560167, 1903783979, 1903785003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1903851563, 1887075375, 1887076399, 1299874863, 1283098675, 1283099699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1283166259, 1266390071, 1870370871, 1870371895, 1853595707, 1803265083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1786488891, 1618717759, 1618718783, 1400615999, 1383905347, 1451015235], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1451016259, 17775166823, 1099939231119, 1099939232143, 1099872124319, 1099872125343], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099721125315, 1099721126339, 1099570129383, 41723371, 30072791539, 17187963379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 124 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 124 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 124 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 124 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1920560167, 1903783979, 1903785003, 1903851563, 1887075375, 1887076399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1887077423, 1887078451, 1819970611, 1820037171, 1803260983, 1803262007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1803263031, 1601937467, 1601938491, 1752934459, 1736158271, 1518055487], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1518056511, 1501345859, 1098693699, 1098694723, 1100224445771, 1100224446795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099821789611, 1099821790635, 1099821791659, 4538016187, 92056031, 1099603684831], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12943330791, 4353465831, 25777827315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1920628779, 1903852591, 1903853615, 1903854639, 1887078451, 1887079475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1887146035, 1836815415, 1836816439, 1836817463, 1820041275, 1820042299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1836820539, 1585163327, 1585164351, 1467724863, 1451014211, 1451015235], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1199358019, 1100123783523, 1099872122271, 1099872123295, 1099872124319, 1099754679739], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099754680763, 8614811119, 4319912431, 8169968], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1887077423, 1870301235, 1870302259, 1870368819, 1853592631, 1853593655], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1853594679, 1836818491, 1853596731, 1803266107, 1786489919, 1652273215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1652274239, 1417459779, 1417460803, 1417461827, 1099905677719, 1099905678743], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099905679767, 1099687571915, 1099687572939, 41724395, 1099553353195, 17187964403], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8598100467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1836814387, 1820038199, 1820039223, 1820040247, 1803264059, 1769710651], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1769711675, 1752935487, 1669050431, 1669051455, 1434236995, 1434238019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1501347907, 1099888900507, 1099888901531, 1099536581035, 1099788239283, 1099670794703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099670795727, 4370245091, 75279843, 12926554603, 4336689643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group13
