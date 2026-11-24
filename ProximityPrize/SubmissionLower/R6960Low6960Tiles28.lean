import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass28

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group28
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [40856390663, 49379423255, 40722392103, 23492201523, 14868718651, 6262010943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950268483, 1950269507, 1916716103, 1883162695, 1866386503, 1816055883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099599630847, 1099566075399, 1099549297163, 4113936], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 132 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 132 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 132 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [45134583819, 45067682843, 32115683371, 19197235251, 10573751355, 6262009919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950267459, 1933491267, 1899937859, 1849607239, 1816053831, 1782500423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732169803, 1099683516907, 1099649961459, 1099616406011, 1099582850563, 1099549295115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4111888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 132 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 132 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 132 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49412908047, 40755942431, 27803941935, 14885492791, 6278785083, 1967042623], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1967043647, 1899935811, 1866382403, 1832828995, 1782498375, 1732167751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1715391559, 1665060939, 1099750625755, 1099717070307, 1099700292071, 1099649959411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616403963, 1099582848515, 1099549293067], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 132 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 132 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 132 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49396199443, 36444200995, 23508976687, 10590526519, 1983817787, 1967041599], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1967042623, 1916711999, 1849604163, 1816050755, 1765720131, 1715389511], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681836103, 1648282695, 1597952075, 1099817734603, 1099784179155, 1099750623707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717068259, 1099683512811, 1099633180151, 1099599624703, 1099549292043], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 132 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 132 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 132 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45084458007, 32132458535, 19197233203, 10590526519, 1983817787, 1967041599], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916710975, 1883157567, 1816049731, 1765719107, 1732165699, 1681835079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631504455, 1597951047, 1547620427, 1099868066239, 1099834510791, 1099800955343], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750622683, 1099717067235, 1099683511787, 1099633179127, 1099582846467, 1099549291019], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [45067683867, 27820717099, 14902267955, 6278783035, 1983817787, 1950264383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1899933759, 1849603135, 1782495299, 1732164675, 1698611267, 1631503431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1597950023, 1564396615, 1514065995, 1099901620663, 1099868065215, 1099834509767], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800954319, 1099750621659, 1099717066211, 1099666733551, 1099616400891, 1099566068231], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4107792], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [40755942431, 23508974639, 10590524471, 6278783035, 1983817787, 1933487167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1883156543, 1832825919, 1765718083, 1715387459, 1665056835, 1614726215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1564395591, 1530842183, 1480511563, 1099935175087, 1099901619639, 1099868064191], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817731531, 1099784176083, 1099733843423, 1099683510763, 1099633178103, 1099582845443], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532512783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [36444200995, 19214009391, 10590525495, 1983816761, 1983817787, 1933487167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1866379327, 1816048703, 1748940867, 1698610243, 1648279619, 1597948999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547618375, 1514064967, 1463734347, 1099951952299, 1099918396851, 1099884841403], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834508743, 1099800953295, 1099750620635, 1099700287975, 1099649955315, 1099599622655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532512783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [32132459559, 14902266929, 6295559221, 1983816761, 1983817787, 1933487167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1866379327, 1816048703, 1748940867, 1698610243, 1648279619, 1581171783], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1530841159, 1497287751, 1446957131, 1099968729511, 1099935174063, 1099901618615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851285955, 1099800953295, 1099750620635, 1099700287975, 1099649955315, 1099599622655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532512783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27820718123, 10590524469, 6278783035, 1983817787, 1933487167, 1866379327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1816048703, 1748940867, 1681833027, 1631502403, 1581171783, 1530841159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480510535, 1430179915, 1099985506723, 1099951951275, 1099901618615, 1099851285955], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817730507, 1099767397847, 1099700287975, 1099649955315, 1099599622655, 1099532512783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19214009389, 10590525495, 1983816761, 1983817787, 1933487167, 1883156543], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1816048703, 1748940867, 1698610243, 1631502403, 1581171783, 1530841159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480510535, 1430179915, 1099985506723, 1099951951275, 1099901618615, 1099851285955], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817730507, 1099750620635, 1099700287975, 1099649955315, 1099582845443, 1099532512783], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14902267955, 6278783035, 1983817787, 1950264383, 1883156543, 1816048703], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1748940867, 1698610243, 1648279619, 1581171783, 1530841159, 1480510535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1413402697, 1100002283935, 1099951951275, 1099901618615, 1099851285955, 1099800953295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750620635, 1099700287975, 1099649955315, 1099582845443, 4107792], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [10590526519, 1983817787, 1967041599, 1899933759, 1832825919, 1748940867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1698610243, 1648279619, 1581171783, 1530841159, 1480510533, 1413402697], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002283935, 1099951951275, 1099901618615, 1099851285955, 1099800953295, 1099750620635], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700287975, 1099633178103, 1099566068231], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 28 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤141 ∧ 7+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group28
