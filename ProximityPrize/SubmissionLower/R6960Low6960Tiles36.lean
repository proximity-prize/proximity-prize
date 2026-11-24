import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass36

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group36
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27822394375, 40658544659, 32018288671, 19083063339, 10476356655, 6164615219], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1852872759, 1852873783, 1802543163, 1768989755, 1735436347, 1685105727], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1651552319, 1617998911, 1567668291, 1550892099, 1517338691, 1483785287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1450231879, 1433455687, 1399902283, 1383126091, 1099888121239, 1099871343003], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099854564767, 1099837786531, 1099804231083, 1099787452847, 1099753897399, 1099737119163], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099703563715, 1099670008267, 1099636452819, 1099602897371, 1099569341923, 1099535786475], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 123 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 123 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 123 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32100587531, 40641771543, 27706548259, 14771321903, 6164614195, 6147839031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1852873783, 1802543163, 1768989755, 1718659131, 1668328511, 1634775103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1601221695, 1567668291, 1534114883, 1500561475, 1467008071, 1433454663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1416678471, 1383125067, 1366348875, 1099904898451, 1099888120215, 1099871341979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099854563743, 1099821008295, 1099804230059, 1099770674611, 1099737119163, 1099720340927], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099686785479, 1099653230031, 1099619674583, 1099569341923, 1099535786475], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 123 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 123 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 123 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27788846095, 36330029083, 27689772071, 14771322927, 6164615219, 1852872759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1852873783, 1802543163, 1768989755, 1718659131, 1668328511, 1634775103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1601221695, 1550891075, 1517337667, 1500561475, 1450230855, 1433454663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1399901255, 1366347851, 1349571659, 1099921675663, 1099904897427, 1099888119191], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099854563743, 1099837785507, 1099804230059, 1099787451823, 1099753896375, 1099720340927], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099686785479, 1099653230031, 1099619674583, 1099569341923, 1099535786475], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 123 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 123 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 123 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40658546707, 32001513507, 19083065387, 10459581491, 1852872759, 1852873783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1819320379, 1785766971, 1735436347, 1685105727, 1634775103, 1601221695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1550891075, 1517337667, 1500561475, 1450230855, 1416677447, 1399901255], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1366347851, 1332794443, 1099938452875, 1099904897427, 1099888119191, 1099871340955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099837785507, 1099804230059, 1099787451823, 1099753896375, 1099720340927, 1099686785479], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099636452819, 1099602897371, 1099552564711, 7381484], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 123 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 123 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 123 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40641772567, 27689772071, 14771322927, 10459582515, 1852873783, 1836097595], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1802544187, 1752213563, 1685105727, 1651552319, 1617998911, 1567668291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1534114883, 1500561475, 1450230855, 1416677447, 1399901255, 1349570635], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1332794443, 1099938452875, 1099921674639, 1099888119191, 1099871340955, 1099837785507], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099804230059, 1099770674611, 1099737119163, 1099703563715, 1099670008267, 1099636452819], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099586120159, 1099535787499], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 123 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 123 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 123 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 123 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 123 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [40624998427, 23378030635, 14754547763, 6147840055, 1836097595, 1819321403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1768990779, 1701882943, 1668329535, 1634776127, 1567668291, 1534114883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1500561475, 1450230855, 1433454663, 1399901255, 1349570635, 1332794443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099938452875, 1099921674639, 1099888119191, 1099854563743, 1099837785507, 1099804230059], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099770674611, 1099737119163, 1099686786503, 1099653231055, 1099619675607, 1099569342947], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [7382508], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 123 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 123 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 123 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 123 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 123 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [36313256991, 23378032683, 10459582515, 6147841079, 1836098619, 1785767995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1735437375, 1685106751, 1651553343, 1584445507, 1550892099, 1517338691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1467008071, 1433454663, 1399901255, 1366347851, 1332794443, 1099938452875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099904897427, 1099888119191, 1099854563743, 1099821008295, 1099787452847, 1099753897399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099720341951, 1099670009291, 1099636453843, 1099586121183, 1099552565735], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 123 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 123 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 123 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 123 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 123 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [32001515555, 19066290223, 10442806327, 1836097595, 1836098619, 1819322427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1752214591, 1701883967, 1668330559, 1601222723, 1567669315, 1534115907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1483785287, 1450231879, 1416678471, 1366347851, 1332794443, 1099938452875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099904897427, 1099871341979, 1099837786531, 1099804231083, 1099770675635, 1099737120187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099703564739, 1099653232079, 1099619676631, 1099569343971, 7383532], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 123 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 123 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 123 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 123 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27689774119, 14754547763, 10442807351, 1836098619, 1836099643, 1768991807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1735438399, 1685107775, 1617999939, 1584446531, 1550893123, 1483785287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1450231879, 1416678471, 1383125067, 1349571659, 1099921675663, 1099888120215], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099871341979, 1099837786531, 1099804231083, 1099753898423, 1099720342975, 1099686787527], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099636454867, 1099586122207, 1099552566759], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27672999979, 10442806327, 6131064891, 1836099643, 1802546239, 1752215615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1701884991, 1651554371, 1601223747, 1567670339, 1500562503, 1467009095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1433455687, 1383125067, 1349571659, 1099921675663, 1099888120215, 1099854564767], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099821009319, 1099787453871, 1099737121211, 1099703565763, 1099653233103, 1099619677655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099569344995, 7384556], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19066291247, 10442807351, 6131065915, 1819323455, 1768992831, 1735439423], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1668331587, 1618000963, 1584447555, 1517339719, 1483786311, 1450232903], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1399902283, 1366348875, 1099904898451, 1099871343003, 1099837787555, 1099804232107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770676659, 1099720343999, 1099686788551, 1099636455891, 1099586123231, 1099552567783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14754549811, 6131064891, 1836099643, 1819323455, 1802547263, 1752216639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1685108803, 1634778179, 1601224771, 1534116935, 1500563527, 1467010119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1416679499, 1383126091, 1099888121239, 1099854565791, 1099821010343, 1099787454895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099753899447, 1099703566787, 1099670011339, 1099619678679, 1099569346019, 7385580], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤123) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 36 where
  orders := orders
  covers := by
    intro a ha box
    change 18+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group36
