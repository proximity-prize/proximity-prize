import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass35

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group35
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23559277575, 23525729295, 14902246423, 6278761503, 36346024991, 23410800683], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10492350515, 6180609079, 1868866619, 1852090427, 1801759807, 1768206399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1734652991, 1684322371, 1650768963, 1617215555, 1583662151, 1550108743], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1533332551, 1499779147, 1483002955, 1099820225967, 1099803447731, 1099786669495], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099769891259, 1099736335811, 1099719557575, 1099686002127, 1099652446679, 1099618891231], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099585335783, 1099551780335, 6597108], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 125 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 125 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 125 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23542503435, 19213987859, 10590503963, 1983795231, 36346024991, 19115833387], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10492349491, 6180608055, 1868865595, 1868866619, 1818535995, 1768205375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1734651967, 1701098559, 1650767939, 1617214531, 1583661123, 1550107719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1516554311, 1499778119, 1449447499, 1432671307, 1099870557603, 1099853779367], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099820223919, 1099803445683, 1099769890235, 1099753111999, 1099719556551, 1099686001103], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099652445655, 1099618890207, 1099585334759, 1099551779311], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 125 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 125 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 125 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23525729295, 14902246423, 6278761503, 36346024991, 19115833387, 10492349491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6180608055, 1868865595, 1852089403, 1801758779, 1751428159, 1717874751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1684321343, 1633990723, 1600437315, 1566883907, 1516553287, 1482999879], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1466223687, 1432670283, 1399116875, 1099904112027, 1099870556579, 1099853778343], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099837000107, 1099803444659, 1099769889211, 1099736333763, 1099702778315, 1099669222867], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099635667419, 1099602111971, 1099568556523, 6596084], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 125 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 125 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 125 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [19213987859, 10590503963, 1983795229, 36346024991, 19115833387, 10492349491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6180608055, 1868865595, 1852089403, 1801758779, 1734650943, 1701097535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1667544127, 1617213507, 1583660099, 1550106691, 1499776071, 1466222663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1449446471, 1399115851, 1382339659, 1099920889239, 1099904111003, 1099870555555], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099853777319, 1099820221871, 1099786666423, 1099753110975, 1099719555527, 1099686000079], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099652444631, 1099618889183, 1099568556523, 6596084], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [14902246423, 6278761503, 36346024991, 19115833387, 10492349491, 6180608055], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1868865595, 1852089403, 1801758779, 1734650943, 1701097535, 1650766911], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1600436291, 1566882883, 1533329475, 1482998855, 1449445447, 1432669255], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1382338635, 1348785227, 1099954443663, 1099920888215, 1099887332767, 1099870554531], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099836999083, 1099803443635, 1099769888187, 1099736332739, 1099702777291, 1099652444631], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099618889183, 1099568556523, 6596084], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [10590504987, 36346024991, 23410800683, 10492350515, 1885641783, 1868865595], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1852089403, 1801758779, 1734650943, 1701097535, 1650766911, 1600436291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1566882883, 1533329475, 1482998855, 1449445447, 1415892039, 1365561419], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1348785227, 1099954443663, 1099937665427, 1099904109979, 1099870554531, 1099836999083], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099803443635, 1099769888187, 1099736332739, 1099702777291, 1099652444631, 1099618889183], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099568556523, 6596084], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [36346024991, 23410800683, 10492350515, 6180609079, 1868866619, 1818535995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1751428159, 1701097535, 1667544127, 1600436291, 1566882883, 1533329475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482998855, 1449445447, 1415892039, 1365561419, 1332008011, 1099971220875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937665427, 1099904109979, 1099870554531, 1099836999083, 1099803443635, 1099769888187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099736332739, 1099686000079, 1099652444631, 1099602111971, 1099551779311], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 125 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [32034283555, 19099058223, 10475574327, 1868865595, 1868866619, 1835313211], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1768205375, 1717874751, 1667544127, 1617213507, 1566882883, 1533329475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482998855, 1449445447, 1415892039, 1365561419, 1332008011, 1099971220875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937665427, 1099904109979, 1099870554531, 1099836999083, 1099803443635, 1099769888187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099719555527, 1099686000079, 1099635667419, 1099585334759, 1099535002099], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27722542119, 14787315763, 6180608055, 1868865595, 1868866619, 1852090427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1784982591, 1734651967, 1684321343, 1617213507, 1583660099, 1533329475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482998855, 1449445447, 1415892039, 1365561419, 1332008011, 1099971220875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937665427, 1099904109979, 1099870554531, 1099836999083, 1099803443635, 1099753110975], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099719555527, 1099669222867, 1099618890207, 1099568557547, 6597108], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23410800683, 14787317811, 6163832891, 1868867643, 1801759807, 1751429183], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1701098559, 1633990723, 1583660099, 1550106691, 1482998855, 1449445447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1415892039, 1365561419, 1332008011, 1099971220875, 1099937665427, 1099904109979], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099870554531, 1099836999083, 1099786666423, 1099753110975, 1099702778315, 1099652445655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099602112995, 1099551780335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19099059247, 10475575351, 1868866619, 1868867643, 1818537023, 1768206399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1717875775, 1650767939, 1600437315, 1566883907, 1499776071, 1466222663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1415892039, 1365561419, 1332008011, 1099971220875, 1099937665427, 1099904109979], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099853777319, 1099820221871, 1099769889211, 1099736333763, 1099686001103, 1099635668443], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099585335783, 1099535003123], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14787317811, 6163832891, 1868867643, 1835314239, 1784983615, 1734652991], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1667545155, 1617214531, 1566883907, 1516553287, 1466222663, 1432669255], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1382338635, 1348785227, 1099954443663, 1099920888215, 1099887332767, 1099853777319], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099803444659, 1099769889211, 1099719556551, 1099669223891, 1099618891231, 1099568558571], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6598132], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 35 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group35
