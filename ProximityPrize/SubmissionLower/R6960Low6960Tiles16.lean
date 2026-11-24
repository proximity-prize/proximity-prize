import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass16

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [40741964807, 75036046359, 83525729327], by decide +kernel⟩
private def batches : List P := [p0]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [57872357387, 83508809759, 44820766779, 77385257447, 47320636903, 60154911219], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i46 : checks (tilesOf batches) 125 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [66429068303, 87652852775, 19017480259, 77502768587, 25963246027, 68761691631], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i49 : checks (tilesOf batches) 125 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [70757855251, 87585813547, 1820837959, 73258137023, 13128678847], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [75019402263, 74868753455, 68778690027, 59296235, 73023176183], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [75019470875, 62034186291], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [79197066271, 44820766779, 73107068387, 47337414115], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [79180357667, 31919156287, 73107136995, 34452515299], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [79146871847, 19017480259, 73123917279, 21584393695], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74868684843, 10427547715, 68795398631, 12960972263], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [70624117807, 1820837959, 68728358391], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [62034186291], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤50) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤136 ∧ 7+a.j≤57 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group16
