import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass23

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group23
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231569413, 2214924297, 2214925321, 1896159243, 1426398223, 1141186575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [956638223, 805644305, 721759249, 654651409, 587543573, 537212949], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [503659541, 1175207961, 1108100121, 1040992281, 27903609885, 19280128037], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [32132529197, 19214081077, 10590597181, 6278855745, 1967113285, 1967114309], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1933560901, 1900007497, 1866454089, 1832900681, 31712033937, 35973445785], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [35923113125, 35872780465, 35805670593, 35721783509, 1225532661, 1040982305], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [5050735973, 4597750225, 1099616475651, 1099582920203, 1099549364755, 1099532586519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i51 : checks (tilesOf batches) 134 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1912936459, 1426398223, 1141186575, 939861005, 805644305, 704982033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [637874193, 553989141, 503658517, 470105109, 1158430745, 1074545689], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1007437849, 27903609885, 14985160741, 32149305385, 19214080053, 10590596157], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [6278854721, 1983889473, 1950336069, 1916782661, 1883229253, 1832898633], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1799345225, 1782569033, 31745588361, 31712032913, 35956667549, 35889557677], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [35822447805, 35721783509, 1242309873, 1040982305, 5050735973, 4580973013], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099666807287, 1099650029051, 1099616473603, 1099582918155, 1099549362707, 4179480], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i54 : checks (tilesOf batches) 134 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [956638221, 805644305, 721759249, 637874193, 553989141, 503658517], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [453327893, 1141653529, 1057768473, 990660633, 27903609885, 14985160741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [32149305385, 19214080053, 6295628861, 6295630909, 1983888449, 1950335041], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1900004421, 1866451013, 1832897605, 1782566985, 1749013577, 1715460169], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [31762365573, 31712032913, 35956667549, 35889557677, 35805670593, 35721783509], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1225532661, 1099733916135, 1099700360687, 1099666805239, 1099633249791, 1099599694343], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099566138895, 1099532583447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i49 : checks (tilesOf batches) 134 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [637874193, 553989141, 503658517, 453327893, 1141653529, 1057768473], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [990660633, 27903609885, 14985160741, 27854338089, 19214079029, 10607372345], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2000663613, 1983887425, 1950334017, 1916780609, 1849672773, 1816119365], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1782565957, 1732235337, 1698681929, 1681905737, 31762365573, 31712032913], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [35956667549, 35889557677, 1099767470559, 1099750692323, 1099717136875, 1099683581427], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099650025979, 1099616470531, 1099566137871, 1099532582423], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 134 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [453327893, 1158430745, 1074545689, 990660633, 27903609885, 14985160741], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [27854338089, 19214079029, 6312405049, 2000662589, 2000663613, 1967110209], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1916779585, 1883226177, 1832895557, 1782564933, 1749011525, 1698680905], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1665127497, 1631574089, 31762365573, 1099817802195, 1099784246747, 1099750691299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099717135851, 1099683580403, 1099633247743, 1099599692295, 1099566136847, 4176408], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1007437849, 27903609885, 14985160741, 27854338089, 14919111733, 10607371321], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2000662589, 2000663613, 1950332993, 1900002369, 1866448961, 1799341125], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1765787717, 1732234309, 1681903689, 1648350281, 1614796873, 26896976141], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834579407, 1099801023959, 1099767468511, 1099733913063, 1099700357615, 1099666802167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616469507, 1099582914059, 1099532581399], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [23608644637, 14985161765, 27837561901, 14919112757, 6312405049, 2000662589], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2000663613, 1933555777, 1883225153, 1849671745, 1782563909, 1749010501], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1715457093, 1648349257, 1614795849, 1581242441, 1099868133831, 1099834578383], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801022935, 1099750690275, 1099717134827, 1099683579379, 1099633246719, 1099599691271], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [19296903201, 32149304361, 14919111733, 6312404025, 6295628861, 2000663613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933555777, 1883225153, 1832894529, 1782563909, 1732233285, 1698679877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631572041, 1598018633, 1564465225, 1099884911043, 1099851355595, 1099817800147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767467487, 1099733912039, 1099683579379, 1099650023931, 1099599691271, 1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [14985161765, 27837561901, 14919112757, 6312405049, 2000662589, 2000663613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933555777, 1883225153, 1832894529, 1765786693, 1732233285, 1681902661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631572041, 1598018633, 1547688009, 1099901688255, 1099851355595, 1099817800147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784244699, 1099733912039, 1099700356591, 1099650023931, 1099599691271, 1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27854338089, 14919111733, 10607371321, 2000662589, 2000663613, 1933555777], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1883225153, 1832894529, 1765786693, 1715456069, 1681902661, 1614794825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1581241417, 1547688009, 1099901688255, 1099868132807, 1099834577359, 1099784244699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750689251, 1099700356591, 1099650023931, 1099599691271, 1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [23542596653, 14919113781, 6295628861, 2000663613, 1933555777, 1883225153], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832894529, 1765786693, 1715456069, 1681902661, 1614794825, 1581241417], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547688009, 1099901688255, 1099868132807, 1099834577359, 1099784244699, 1099750689251], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700356591, 1099650023931, 1099599691271, 1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [19230855217, 10607371321, 2000662589, 2000663613, 1933555777, 1883225153], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832894529, 1765786693, 1732233285, 1681902661, 1614794825, 1581241417], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547688009, 1099901688255, 1099868132807, 1099834577359, 1099784244699, 1099733912039], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700356591, 1099650023931, 1099599691271, 1099549358611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [14919113781, 6295628861, 2000663613, 1950332993, 1900002369, 1849671745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1782563909, 1732233285, 1681902661, 1614794825, 1581241417, 1547688009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901688255, 1099868132807, 1099834577359, 1099784244699, 1099733912039, 1099683579379], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633246719, 1099582914059, 1099532581399], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 23 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 5+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group23
