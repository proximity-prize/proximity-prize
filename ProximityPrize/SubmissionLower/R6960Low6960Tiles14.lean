import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [32103664647, 49133595667, 87050443811, 18935099455, 43714960695, 35057994039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22156324151, 47338696151, 12962409947, 30125492703, 17240599007, 4338990563], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 122 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 122 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 122 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40677480459, 49150574619, 86966628395, 39419998507, 34957334827, 5110742315], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21686557115, 13079851451, 47288435171, 34403611107, 21518783971, 12895367659], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 122 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 122 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 122 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49116685327, 61599339551, 52892176435, 26249957751, 17592921463, 497009015], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43412903295, 30528143743, 47372248527, 12962409947, 4372544987, 17190265323], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i9 : checks (tilesOf batches) 122 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 122 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 122 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49234325523, 61549076515, 40107940919, 43429749111, 26266733943, 17509034387], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4674534803, 12928854499, 8633956835, 38665019883, 25780193771], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 122 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 122 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 122 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53395143703, 57254178859, 27340482619, 39084454271, 21938215295, 13079851443], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [245350835, 47355542995, 38765686227, 8633889251, 4338990563, 21502006759], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 122 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 122 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 122 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 122 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 122 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53412055067, 57170295855, 14606578751, 34890218863, 21954994543, 47321991643], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34437233115, 8667511259, 17223819747, 8633955811], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 122 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 122 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 122 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 122 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53344949279, 57069635635, 1788788803, 30679140699, 17777469787, 4909415771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47372391887, 30192600527, 12895300075, 8600402411], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 122 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 122 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 122 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 122 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53294686243, 48580432951, 26266735991, 13381841271, 497009015, 47405949383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25931190727], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 122 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 122 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 122 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 122 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [53227645991, 35863306299, 21787222435, 8902392227, 43161316795, 25981524411], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [53110208555, 23162956863, 43245271459, 21787223459, 4406099411, 38665091563], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21485232619], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [57187075119, 6083755075, 39151633779, 21904665971, 17257377243, 34370127339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17190267371], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [52908953651, 34823115131, 13365065083, 30075163115, 17190334955], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤122) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group14
