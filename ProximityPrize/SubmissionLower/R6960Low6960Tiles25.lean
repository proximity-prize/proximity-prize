import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass25

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group25
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10905848837, 6594238473, 2282496013, 2282497037, 2014062609, 1795959825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1628188689, 36611044375, 23675820065, 36528222251, 23592997943, 14969515071], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6362807363, 2051064903, 2034288711, 2000735303, 1950404683, 1916851275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34983653785, 34815880641, 34597775861, 1099616540183, 1099582984735, 1099549429287], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4246060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6594238473, 2282496013, 2282497037, 2014062609, 1795959825, 1628188689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [32316077077, 23692596253, 36544998439, 23609774131, 10691323963, 6379582527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2067840067, 2034286659, 1983956039, 1950402631, 1916849223, 1866518603], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1832965195, 34983653787, 34815880641, 34597775861, 1099700426243, 1099666870795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099633315347, 1099599759899, 1099566204451, 1099532649003], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2282497037, 2047617041, 1812737041, 1644965905, 32316077077, 23692596253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [32250031141, 19314805809, 10691321913, 6379580477, 2084615229, 2051061827], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2000731201, 1967177795, 1900069957, 1866516549, 1832963141, 1782632521], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1749079113, 30671909277, 34799103429, 1099784312303, 1099750756855, 34564221437], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099717201407, 1099683645959, 1099650090511, 1099599757851, 1099566202403, 4241964], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1661743121, 32316077077, 23692596253, 32250031141, 19314805809, 10691321913], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2084613181, 2084614205, 2067838013, 2000730177, 1950399553, 1916846145], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1866515525, 1832962117, 1799408709, 1749078089, 1715524681, 30655132065], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817866727, 1099784311279, 1099750755831, 1099717200383, 1099683644935, 1099650089487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616534039, 1099566201379, 4240940], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [32316079125, 19380853793, 32233254955, 15019839537, 6396354617, 6396356665], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2084614205, 2034283581, 1967175745, 1933622337, 1883291713, 1832961093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1799407685, 1765854277, 1715523657, 1681970249, 1099851421151, 1099817865703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784310255, 1099750754807, 1099717199359, 1099683643911, 1099633311251, 1099599755803], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549423143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [28004337689, 36544996389, 19314804785, 10708098101, 2101389369, 2084613181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2067836989, 2017506365, 1950398529, 1916845121, 1866514497, 1816183877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1765853253, 1732299845, 1681969225, 1648415817, 1099884975575, 1099851420127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817864679, 1099784309231, 1099733976571, 1099700421123, 1099650088463, 1099616533015], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566200355, 4239916], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [23692596253, 32250031141, 19314805809, 6396354617, 2101389369, 2084613181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2067836989, 2000729149, 1950398529, 1900067905, 1849737281, 1799406661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1749076037, 1715522629, 1665192009, 1631638601, 1099901752787, 1099868197339], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834641891, 1099801086443, 1099750753783, 1099717198335, 1099666865675, 1099616533015], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582977567, 4239916], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [19380854817, 27938288681, 15019839537, 6396354617, 2101389369, 2084613181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2051059773, 2000729149, 1933621313, 1883290689, 1849737281, 1782629445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732298821, 1698745413, 1648414793, 1614861385, 1099918529999, 1099884974551], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851419103, 1099817863655, 1099767530995, 1099717198335, 1099683642887, 1099633310227], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582977567, 1099532644907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [32250031141, 19314805809, 6396354617, 2101389369, 2084613181, 2051059773], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2000729149, 1933621313, 1883290689, 1832960065, 1782629445, 1732298821], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1698745413, 1631637577, 1598084169, 1099935307211, 1099901751763, 1099851419103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817863655, 1099767530995, 1099733975547, 1099683642887, 1099633310227, 1099582977567], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532644907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27938289705, 15003063349, 6396355641, 2084613181, 2067836989, 2000729149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933621313, 1883290689, 1832960065, 1782629445, 1732298821, 1681968197], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631637577, 1598084169, 1099935307211, 1099901751763, 1099868196315, 1099817863655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767530995, 1099733975547, 1099683642887, 1099633310227, 1099582977567, 4239916], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [23626548269, 10708098101, 2101389369, 2084613181, 2067836989, 2017506365], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950398529, 1883290689, 1832960065, 1782629445, 1732298821, 1681968197], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631637577, 1581306953, 1099952084423, 1099901751763, 1099868196315, 1099817863655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767530995, 1099733975547, 1099683642887, 1099616533015, 1099566200355, 4239916], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [15019839537, 10691321913, 2084613181, 2084614205, 2017506365, 1950398529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1900067905, 1849737281, 1782629445, 1732298821, 1681968197, 1631637577], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1581306953, 1099952084423, 1099901751763, 1099868196315, 1099817863655, 1099767530995], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717198335, 1099666865675, 1099616533015, 1099566200355], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [10708098101, 6396356665, 2084614205, 2034283581, 1967175745, 1900067905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1849737281, 1782629445, 1732298821, 1698745413, 1631637577, 1581306953], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952084423, 1099901751763, 1099851419103, 1099817863655, 1099767530995, 1099717198335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666865675, 1099599755803, 1099549423143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 25 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 6+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group25
