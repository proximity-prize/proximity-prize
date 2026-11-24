import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass5

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [1897270279, 1880494091, 1880495115, 1882134539, 1865358351, 1865359375], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [49278428175, 87380415519, 32016017465, 60704839043, 1100087136643, 1100087137667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100087138691, 1100087139715, 1100087140739, 1100087141763, 43205922255, 60218292727], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40620726283, 57785139227, 1464498219, 1447787567, 1447788591, 1447789615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1431013427, 1431079987, 1431081011, 1414304823, 1414305847, 1414306871], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1397530683, 1397597243, 1397598267, 1380822079, 1380823103, 1380824127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1364047939, 1364048963, 1364115523, 1347339335, 52081490315, 26311830921], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [51712104931, 55956950511], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [45084124175, 2068205599, 2068272159, 2051495971, 2051562531, 2051563555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2034852903, 2034853927, 2034854951, 2018144299, 2018145323, 2018146347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2001435695, 2001436719, 2001437743, 1514899507, 1514966067, 1514967091], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1498190903, 1498191927, 1498192951, 1481416763, 1481483323, 1481484347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1464708159, 1464709183, 1699591231, 1682815043, 1682816067, 1682882627], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1666106439, 43407739295, 17403131349], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1967075347, 1950299159, 1950300183, 1950497815, 1933787163, 1933788187], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933920283, 1917144095, 1917210655, 1917277215, 1900501027, 1900567587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1900568611, 1883857959, 2018076711, 2018077735, 2001367083, 2001368107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2001369131, 1984658479, 1984659503, 1984660527, 1967884339, 1967950899], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1967951923, 1951175735, 1397528631, 1397529655, 1380753467, 1380820027], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1380821051, 27704273983, 34918472071, 55973589483, 47249648139], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53540437015, 87095406633, 1900987461, 48004559179, 1100322021707, 1100322022731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100322023755, 1100322024779, 1100322025803, 1100322026827, 1100322027851, 1100322028875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [5105434953, 55923326455, 42988238339], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [2017806363, 2001030175, 2001096735, 2001163295, 1984387107, 1984453667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1984454691, 1967744039, 1967745063, 1967746087, 1951035435, 1951036459], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1951037483, 78572649517, 43642551647, 30707460447, 25842067963, 72336889], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55889840639, 1099533484551, 1099533485575, 1099533486599, 1099533487623, 1099533488647], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099533489671, 1099533490695, 1099533557255, 1099533558279, 1099533559303], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1833391135, 1816614947, 1816681507, 1816682531, 1799971879, 1799972903], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1799973927, 1783263275, 1783264299, 1783265323, 1766554671, 1766555695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1766556719, 1749780531, 61560622129, 34901691787, 1100053655947, 1100053656971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100053657995, 1100053659019, 1100053660043, 1100053661067, 51762648535, 34582923733], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1447583779, 1430873127, 1430874151, 1430875175, 1414164523, 1414165547], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1414166571, 1397455919, 1397456943, 1397457967, 1380681779, 1380748339], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1967951923, 1951175735, 1951176759, 1951177783, 1934401595, 1934468155], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1934469179, 1917692991, 1917694015, 1699591231, 1682815043, 1682816067], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1682882627, 1666106439, 47836782973, 17403131351, 30069854729, 17185026569], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [2034854951, 2018144299, 2018145323, 2018146347, 2001435695, 2001436719], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2001437743, 1984661555, 1984728115, 1984729139, 1967952951, 1967953975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1263311927, 1246535739, 1246602299, 1246603323, 1229827135, 1229828159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [19080787007, 47887117671, 30690614631, 25825287677, 12906838533], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78522251305, 1900987461, 43726436687, 1100254913871, 1100254980431, 1100254981455], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100254982479, 1100254983503, 1100254984527, 1100254985551, 5088657741, 21513545217], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8628649473, 42954750475], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [70016271405, 659326311, 659392871, 659393895, 1100171022695, 1100171023719], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100171024743, 1100171025767, 1100171026791, 1100171027815, 1100171094375, 1100187872615], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100187873639, 1100187874663, 1100187875687, 1100187876711, 1100187877735, 693028197], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38676563463, 17185025545, 4300128777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1967951923, 1951175735, 1951176759, 1951177783, 1934401595, 1934468155], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1934469179, 1917692991, 1917694015, 1917695039, 1900918851, 1900919875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1900986435, 1900987463, 30069854729, 17185026569], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1598856247, 1582080059, 1582146619, 1582147643, 1565371455, 1565372479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1565373503, 1548597315, 1548598339, 1548664899, 1531888711, 26127211957], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13242382773], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 6+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group5
