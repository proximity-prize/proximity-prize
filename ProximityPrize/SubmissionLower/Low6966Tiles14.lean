import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14898891781, 40586845197, 82984125465, 78807209013, 64966116709, 60654454117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30371660189, 55872921053, 60134426085], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i51 : checks (tilesOf batches) 121 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36224374793, 70233308181, 87262855213, 10322826313, 56309154165, 39129364853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [64848674177, 56258821505, 55956806091], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i54 : checks (tilesOf batches) 121 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44915762189, 74478211101, 74428422197, 60570489213, 51963858301, 30455546249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60134335973, 51544493541], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i49 : checks (tilesOf batches) 121 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49211125777, 82934128673, 48843239485, 60654379361, 47769623905, 17352609213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60151194081, 42971340257, 21496580577], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i52 : checks (tilesOf batches) 121 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53472869397, 87128567849, 27519468613, 56460144977, 39280355665, 60134342117], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i55 : checks (tilesOf batches) 121 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61828122649, 87078306861, 6027860041, 52148405577, 34951838025, 60352448945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30120065497, 47283078621, 34398254557], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 121 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 121 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 121 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [66005783581, 78521996343, 43524920665, 30589763929, 60453115289, 43273327001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25825100249, 55303641, 25774767589], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 121 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 121 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 121 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 121 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 121 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [70200221729, 61476414521, 39062250877, 17620979069, 56242037125, 43340437893], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21496579553, 38659594725, 25774768613], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 121 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 121 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 121 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 121 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74377817125, 44447609917, 56342703469, 39129359725, 17453272485, 34381473249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21496580577], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87044683819, 18912758853, 52232223037, 35035721021, 34381475297, 51544488421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [12889870821], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [87027975215, 6027860041, 47954101565, 30757532989, 9299481917, 30069732837], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82749853747, 43625582917, 30656871749, 675994949, 25841876437, 4367047125], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69982460983, 39196466533, 22016607589, 541842789], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 121 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [57198225467, 34784061825, 17604201857], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 21+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6966Allocation.Group14
