import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass27

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group27
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [28070513671, 49496795155, 45134731299, 27904541743, 19264282683, 10657575999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2050867267, 2034091079, 2017314887, 1983761479, 1933430859, 1099582788123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099549232675, 4049448], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [28053739529, 49480021015, 36528022567, 23592798259, 14969315387, 6362607679], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2050865219, 2050866243, 2000535619, 1950204999, 1916651591, 1883098183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1832767563, 1099683451395, 1099649895947, 1099616340499, 1099582785051, 1099549229603], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49513571343, 40856540191, 27904539695, 14986090551, 6379382843, 2067640383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2067641407, 2017310787, 1966980163, 1933426755, 1866318919, 1832765511], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1799212103, 1748881483, 1099767337455, 1099733782007, 1099700226559, 1099666671111], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616338451, 1099582783003, 1099532450343], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49496797203, 36544798755, 23609574447, 10691124279, 6379382843, 2067640383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2017309759, 1950201923, 1899871299, 1866317891, 1799210055, 1765656647], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732103239, 1681772619, 1099834446303, 1099800890855, 1099767335407, 1099733779959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683447299, 1099649891851, 1099599559191, 1099549226531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45185055765, 32233056293, 19297830963, 10691124279, 2084415545, 2067639359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2017308735, 1966978111, 1899870275, 1849539651, 1815986243, 1748878407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1715324999, 1681771591, 1631440971, 1099884777939, 1099851222491, 1099817667043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784111595, 1099733778935, 1099700223487, 1099649890827, 1099599558167, 1099549225507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [45168281627, 27921314859, 15002865715, 6379380793, 2084415545, 2050862143], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1983754303, 1933423679, 1866315843, 1815985217, 1765654593, 1715323973], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681770565, 1648217157, 1597886537, 1099918332363, 1099884776915, 1099851221467], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817666019, 1099784110571, 1099733777911, 1099683445251, 1099633112591, 1099582779931], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4042280], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [40856540191, 23609572397, 10691122229, 6379380795, 2084415545, 2034084927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1966977087, 1916646463, 1832761409, 1799208001, 1748877377, 1698546757], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1664993349, 1614662725, 1564332105, 1099951886787, 1099918331339, 1099867998679], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834443231, 1099800887783, 1099750555123, 1099716999675, 1099649889803, 1099599557143], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532447271], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [36544798755, 19314607149, 10691123255, 2084414521, 2084415545, 2017307711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950199869, 1899869245, 1832761409, 1782430785, 1748877377, 1681769541], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1648216133, 1614662725, 1547554889, 1099968663999, 1099918331339, 1099884775891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851220443, 1099800887783, 1099767332335, 1099716999675, 1099666667015, 1099616334355], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549224483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [32233057319, 15002864689, 6396156981, 2084414521, 2084415545, 2017307711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950199869, 1899869245, 1832761409, 1782430785, 1732100161, 1681769541], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1631438917, 1597885509, 1547554889, 1099968663999, 1099935108551, 1099901553103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851220443, 1099817664995, 1099767332335, 1099716999675, 1099666667015, 1099616334355], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549224483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [27921315883, 10691122229, 6379380793, 2084415545, 2017307709, 1950199869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1899869245, 1832761409, 1782430785, 1732100161, 1681769541, 1631438917], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1597885509, 1530777673, 1099985441211, 1099935108551, 1099901553103, 1099851220443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817664995, 1099767332335, 1099716999675, 1099666667015, 1099616334355, 1099549224483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19314607149, 10691123253, 2084414521, 2084415545, 2017307709, 1966977085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916646461, 1832761409, 1782430785, 1748877377, 1681769541, 1631438917], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1597885509, 1530777673, 1099985441211, 1099935108551, 1099901553103, 1099851220443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800887783, 1099767332335, 1099716999675, 1099649889803, 1099599557143, 1099549224483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [15002865713, 6379380793, 2084415545, 2034084925, 1966977085, 1916646461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1849538625, 1799208001, 1748877377, 1681769541, 1631438917, 1597885509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1530777673, 1099985441211, 1099935108551, 1099901553103, 1099851220443, 1099800887783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750555123, 1099700222463, 1099649889803, 1099599557143, 1099532447271], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [6396156981, 2084414521, 2084415545, 2034084925, 1983754301, 1933423677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1849538625, 1799208001, 1748877377, 1681769541, 1648216133, 1597885509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1530777673, 1099985441211, 1099935108551, 1099884775891, 1099851220443, 1099800887783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750555123, 1099700222463, 1099633112591, 1099582779931, 1099532447271], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 27 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 7+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group27
