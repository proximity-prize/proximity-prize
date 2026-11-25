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
  ⟨unpack [31982423047, 49197689875, 125517782051, 48191724811, 48007318795, 22388587787], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34535280067, 21650387395, 38762974675, 38679164391, 8614562279], by decide +kernel⟩
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
private theorem i43 : checks (tilesOf batches) 122 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 122 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40674138123, 57553076251, 91376285739, 1752617035, 43611683143, 34937939271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4990617927, 51765330359, 38880507319, 25878242771, 4403478995, 4319518183], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 122 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49130382351, 74363982879, 57234725943, 47822689635, 34937865571, 26163456391], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13295338887, 47352915411, 21499390439, 12909527527, 7852520], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 122 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49231310867, 87047626787, 31649543231, 47990464823, 35072086327, 17388975547], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8799111611, 30106096099, 41333219, 47252333035], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 122 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 122 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 122 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 122 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53425814551, 91258777643, 10359326791, 43745833259, 30810676523, 9403022635], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51614399963, 25827909087, 58112479, 42957435371], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 122 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 122 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 122 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 122 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 122 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57586698267, 86980657199, 39417381171, 34937940275, 5074505011, 51731843519], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38846954943, 21667162559, 8782266815, 7775720], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 122 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 122 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 122 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 122 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 122 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53375685663, 78457899059, 39283165511, 30575866183, 695652679, 17355420099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8765556163, 51631183319, 34417838559, 58109407], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 122 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 122 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 122 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 122 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61697253411, 57150839863, 30559083891, 17640635763, 511103347, 47587877275], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34703053211, 12926303715, 41405923, 4302747115], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 122 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 122 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 122 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 122 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70085930023, 35877400639, 47772429679, 30592638319, 17405754795, 276287915], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [12926303715, 41405923], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 122 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 122 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 122 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 122 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78508161067, 14620738631, 43628460363, 30676526411, 25827911135, 12943081951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [24629735], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 122 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 122 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 122 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78474675247, 1752617035, 39350273351, 26415115591, 4990617927, 21516168675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [41403875], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 122 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 122 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 122 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69935075379, 34988200279, 26297677143, 628543831, 17271535063, 4386703831], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 122 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 122 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 122 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤122) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 18 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤138 ∧ 6+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group18
