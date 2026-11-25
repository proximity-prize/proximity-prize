import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23338486791, 53388846093, 138483947555, 69546694941, 65201544479, 47367261639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25875725769, 60168445401, 38984153], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 120 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 120 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 120 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 120 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 120 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 120 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 120 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40603883529, 62013128729, 100114725935, 64916323695, 30556667245, 55856601565], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [42971714013], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 120 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 120 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 120 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 120 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 120 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 120 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 120 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49211319309, 74613019679, 66057116727, 69009954207, 56125135263, 8746357181], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i9 : checks (tilesOf batches) 120 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 120 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 120 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 120 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 120 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 120 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [57667432465, 104275339303, 14618250309, 65067247943, 35019401541, 64530428361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [55839912417], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 120 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 120 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 120 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 120 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 120 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 120 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [57768360981, 99997217835, 6011606089, 60755572047, 34985849165], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i15 : checks (tilesOf batches) 120 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 120 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 120 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 120 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 120 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61962864667, 91457684527, 56393499999, 30623776093, 60201912785], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 120 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 120 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 120 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 120 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 120 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [66140525599, 74412102711, 51930830215, 17571170693, 64597546425], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 120 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 120 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 120 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 120 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 120 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [66140659747, 61661487163, 47484871083, 8830243241, 64580772287], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 120 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 120 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 120 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 120 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78740417575, 36109858883, 60554243455, 13309684093], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 120 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 120 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 120 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 120 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87179425835, 14618250309, 60671687007, 22033839453, 60134881763], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 120 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 120 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 120 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 120 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82918081583, 6011606089, 56343168363, 21983509865], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 120 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 120 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 120 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78639960115, 52014715251, 21950023025], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 120 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 120 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 120 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65889344567, 47568756119, 13209095573], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 120 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 120 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤120) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 18+a.b≤138 ∧ 4+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group12
