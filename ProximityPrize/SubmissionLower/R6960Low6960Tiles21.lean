import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass21

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14949288965, 10621099021, 6309357585, 2014392337, 1997616149, 1880176661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [49245142037, 36293143589, 23357919281, 14734436409, 10405918785, 1799210053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1799211077, 1782434885, 1748881481, 1715328073, 1698551881, 1648221261], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38758726105, 1099616345563, 1099582790115, 1099566011879, 1099532456431, 4050416], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i43 : checks (tilesOf batches) 124 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 124 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6342580233, 10621100045, 6309358609, 1997616149, 1863399445, 49245142037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [36293143589, 23357919281, 10439469113, 6127727677, 1815985217, 1815986241], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1782432837, 1748879429, 1715326021, 1681772617, 1648219209, 1631443017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1581112397, 1099683454411, 1099649898963, 38775503317, 1099633120727, 1099599565279], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582787043, 1099549231595, 4048368], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 124 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 124 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [10621101069, 2014392337, 1997616149, 1863399445, 44950174741, 36293142565], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23357918257, 10439468089, 6127726653, 1815984193, 1815985217, 1782431809], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732101189, 1698547781, 1664994373, 1631440969, 1597887561, 1581111369], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1530780749, 1099733786047, 1099700230599, 1099683452363, 1099649896915, 38775503317], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099633118679, 1099599563231, 1099566007783, 1099532452335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 124 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [2014392337, 1997616149, 1896953877, 44950174741, 36293142565, 19062950961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10439467065, 6127725629, 1832760381, 1815984193, 1782430785, 1748877377], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1698546757, 1664993349, 1631439941, 1581109321, 1547555913, 1530779721], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1480449101, 1099784117683, 1099750562235, 1099733783999, 1099700228551, 1099666673103], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099633117655, 34446981597, 1099599562207, 1099566006759, 1099532451311], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 124 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 124 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 124 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 124 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44950174741, 36293142565, 19062950961, 10439467065, 6127725629, 1832760381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1782429761, 1748876353, 1715322945, 1664992325, 1631438917, 1597885509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547554889, 1514001481, 1497225289, 1446894669, 1099817672107, 1099784116659], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767338423, 1099733782975, 1099700227527, 1099666672079, 1099633116631, 1099599561183], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566005735, 1099532450287], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 124 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 124 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 124 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 124 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44933400601, 31981401129, 14751208501, 6144500793, 6127725629, 1832760381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765652545, 1732099137, 1681768513, 1631437893, 1597884485, 1564331077], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1514000457, 1480447049, 1463670857, 1413340237, 1099851226531, 1099817671083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800892847, 1099767337399, 1099733781951, 1099700226503, 1099666671055, 1099633115607], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582782947, 1099549227499], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 124 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 124 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 124 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 124 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 124 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [40621659165, 27669658669, 14751209525, 6144501817, 1832759357, 1815983165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748875329, 1715321921, 1681768513, 1614660677, 1581107269, 1547553861], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1497223241, 1463669833, 1430116425, 1396563021, 1099868003743, 1099851225507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817670059, 1099784114611, 1099750559163, 1099717003715, 1099683448267, 1099633115607], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599560159, 1099566004711, 4044272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 124 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 124 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 124 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 124 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 124 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [36309917729, 23374693421, 10456243253, 6144501817, 1832759357, 1815983165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748875329, 1698544705, 1664991297, 1597883461, 1564330053, 1530776645], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480446025, 1446892617, 1413339209, 1363008589, 1099901558167, 1099868002719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834447271, 1099800891823, 1099767336375, 1099733780927, 1099700225479, 1099649892819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616337371, 1099566004711, 4044272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 124 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 124 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 124 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 124 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [31998176293, 19062950961, 10439467065, 1832758333, 1832759357, 1815983165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748875329, 1698544705, 1664991297, 1597883461, 1564330053, 1513999429], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1463668809, 1430115401, 1396561993, 1346231373, 1099918335379, 1099884779931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851224483, 1099817669035, 1099784113587, 1099733780927, 1099700225479, 1099649892819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616337371, 1099566004711, 4044272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 124 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27686434857, 14751208501, 6144500793, 1832758333, 1832759357, 1815983165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748875329, 1698544705, 1648214081, 1597883461, 1547552837, 1513999429], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1463668809, 1430115401, 1396561993, 1346231373, 1099918335379, 1099884779931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851224483, 1099817669035, 1099784113587, 1099750558139, 1099700225479, 1099666670031], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616337371, 1099566004711, 4044272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 124 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [23374693421, 10456243253, 6144501817, 1832759357, 1815983165, 1748875329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1698544705, 1664991297, 1597883461, 1547552837, 1513999429, 1463668809], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1430115401, 1379784777, 1329454157, 1099935112591, 1099901557143, 1099851224483], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817669035, 1099784113587, 1099750558139, 1099700225479, 1099649892819, 1099616337371], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566004711, 4044272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 124 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [19062951985, 10439468089, 1832759357, 1832760381, 1765652545, 1715321921], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1664991297, 1597883461, 1564330053, 1513999429, 1463668809, 1413338185], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1379784777, 1329454157, 1099935112591, 1099901557143, 1099868001695, 1099817669035], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784113587, 1099733780927, 1099700225479, 1099649892819, 1099599560159, 1099549227499], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 124 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [14751210549, 6127725629, 1832760381, 1765652545, 1715321921, 1664991297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1597883461, 1564330053, 1513999429, 1463668809, 1430115401, 1379784777], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1329454157, 1099935112591, 1099901557143, 1099851224483, 1099817669035, 1099784113587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733780927, 1099700225479, 1099649892819, 1099599560159, 1099549227499], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 124 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 21 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group21
