import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass18

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group18
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10603662341, 1996953609, 1963400207, 1577525263, 1325868047, 1141319697], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1023880209, 923217937, 822555669, 755447829, 705117205, 44882739225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [40537713701, 27585713205, 18962231357, 10338747461, 1732038729, 1732039753], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1715263561, 1681710157, 1648156749, 48473062593, 48422729933, 39765095645], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [39681208561, 39580544265, 39463102757, 39295329613, 39043670409, 1099565949403], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532393955, 38657793509, 3987940], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 121 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 121 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 121 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1996953609, 1980177423, 1577525263, 1309090829, 1141319697, 1007102993], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [906440721, 805778453, 738670613, 671562773, 44882739225, 40537713701], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [23290745909, 14667263037, 6060555329, 6043780165, 1748814917, 1698484297], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1681708105, 1648154697, 1614601293, 1581047885, 44211649721, 44144539849], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [35486905561, 39697985773, 39597321477, 39463102757, 39312106825, 39043670409], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099633058251, 1099599502803, 1099582724567, 1099549169119, 1099532390883], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 121 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 121 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 121 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1325868045, 1141319697, 1007102993, 906440721, 805778453, 721893397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [671562773, 44882739225, 36242746405, 23307522097, 14684039225, 6060554305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1765589057, 1748812869, 1732036677, 1698483269, 1648152649, 1631376457], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1597823049, 1564269645, 1530716237, 44211649721, 44161317061, 35486905561], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [39697985773, 39597321477, 39463102757, 39295329613, 1099683389887, 1099649834439], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099633056203, 1099599500755, 1099582722519, 1099549167071, 3983844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 121 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 121 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 121 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [923217937, 805778453, 738670613, 671562773, 44882739225, 36242746405], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23307522097, 10389071929, 6077330493, 1765588033, 1765589057, 1715258437], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681705029, 1648151621, 1614598217, 1581044809, 1547491401, 1513937997], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1480384589, 44211649721, 44144539849, 35486905561, 39681208561, 1099733721523], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099700166075, 1099683387839, 1099649832391, 1099616276943, 1099599498707, 1099565943259], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532387811], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 121 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 121 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 121 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [671562773, 44882739225, 36242746405, 23307522097, 10389071929, 6077330493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765588033, 1732034625, 1681704005, 1648150597, 1614597189, 1564266569], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547490377, 1513936969, 1463606349, 1446830157, 44211649721, 1099767275947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750497711, 1099716942263, 1099683386815, 1099666608579, 1099633053131, 1099599497683], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565942235, 1099532386787], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 121 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 121 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 121 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 121 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44883003417, 31931003945, 18995778613, 10389071929, 1782363197, 1765587009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748810817, 1715257409, 1664926789, 1631373381, 1597819973, 1547489353], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1513935945, 1480382537, 1430051917, 1413275725, 1099800830371, 1099784052135], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750496687, 1099716941239, 1099683385791, 1099649830343, 1099616274895, 1099582719447], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549163999, 3980772], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 121 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 121 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 121 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [44866229277, 27619262509, 14700813365, 6077328445, 1782363197, 1765587009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1732033601, 1698480193, 1648149573, 1597818949, 1564265541, 1513934921], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480381513, 1463605321, 1413274701, 1379721293, 1099834384795, 1099800829347], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767273899, 1099750495663, 1099716940215, 1099683384767, 1099649829319, 1099599496659], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565941211, 1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 121 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 121 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 121 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 121 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 121 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [40554487841, 23307520049, 14684037177, 6077329469, 1765587009, 1732033601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1681702977, 1631372357, 1597818949, 1547488325, 1497157705, 1463604297], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1430050889, 1396497485, 1362944077, 1099851162007, 1099817606559, 1099800828323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767272875, 1099733717427, 1099700161979, 1099649829319, 1099616273871, 1099582718423], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 121 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 121 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 121 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 121 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 121 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [36242746405, 19012554801, 10389070905, 6077329469, 1765587009, 1732033601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1681702977, 1614595141, 1581041733, 1547488325, 1497157705, 1463604297], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1430050889, 1379720269, 1346166861, 1099867939219, 1099834383771, 1099800828323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767272875, 1099733717427, 1099700161979, 1099666606531, 1099633051083, 1099582718423], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [31931004969, 18995779637, 6077328445, 1782363197, 1765587009, 1732033601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1681702977, 1614595141, 1581041733, 1530711109, 1480380489, 1446827081], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1413273673, 1362943053, 1329389645, 1099884716431, 1099851160983, 1099817605535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784050087, 1099750494639, 1099716939191, 1099666606531, 1099633051083, 1099582718423], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [27619263533, 14684037177, 6077329469, 1765587009, 1732033601, 1681702977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1614595141, 1581041733, 1530711109, 1480380489, 1446827081, 1413273673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1362943053, 1329389645, 1099884716431, 1099851160983, 1099817605535, 1099784050087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750494639, 1099716939191, 1099666606531, 1099633051083, 1099582718423, 1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [23307522097, 10389071929, 1782363197, 1765587009, 1732033601, 1681702977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1614595141, 1581041733, 1530711109, 1480380489, 1446827081, 1396496457], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1346165837, 1312612429, 1099901493643, 1099867938195, 1099834382747, 1099784050087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750494639, 1099716939191, 1099666606531, 1099633051083, 1099582718423, 1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [14700813365, 6077328445, 1782363197, 1765587009, 1732033601, 1681702977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1631372357, 1581041733, 1530711109, 1480380489, 1446827081, 1396496457], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1346165837, 1312612429, 1099901493643, 1099867938195, 1099834382747, 1099784050087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750494639, 1099716939191, 1099666606531, 1099616273871, 1099582718423, 1099532385763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 121 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤121) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 18 where
  orders := orders
  covers := by
    intro a ha box
    change 20+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group18
