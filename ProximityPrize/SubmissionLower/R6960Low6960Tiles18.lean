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
  ⟨unpack [10603662341, 32029874185, 74360240149, 87279501357, 14617662537, 60721281369], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [56426394969, 47668833657, 51560978913, 42971213281], by decide +kernel⟩
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
  ⟨unpack [32029874185, 53355165717, 87195479077, 36058873921, 56409615709, 43491239261], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60251584969, 17235038681, 51560978913, 42971211233], by decide +kernel⟩
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
  ⟨unpack [40637375501, 74377350173, 82850386997, 43508012385, 30606410081, 558424417], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [56375987557, 47786198373, 30069604837], by decide +kernel⟩
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
  ⟨unpack [49110331409, 82866888737, 53003857981, 56443167057, 39280154961, 26076561821], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4601798045, 55923061201, 51544287717], by decide +kernel⟩
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
  ⟨unpack [49194482709, 87061261349, 35907878977, 52232088893, 39296934205, 21647378869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [206168501, 34414830041, 21530002905, 4316585441, 51544354277], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [53355431961, 86994222125, 18845519945, 47953902901, 35001969973, 55939910093], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30153420241, 17268592081, 55173593, 42971202017], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [61727462429, 86977581107, 39380750645, 34901309749, 5037940021, 56141174173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38961384861, 21664151993, 13074223545, 25774568933], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [70116204577, 65637033017, 30639891805, 26210780509, 575201629, 52030759281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39112381809, 17302078921, 8712214985, 38676239841], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [78521658405, 44330039361, 52181757257, 34968412489, 17553737101, 8930253197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30103085533, 17218191837, 8611551713, 51544354277], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [78488172585, 31529026629, 47903570245, 30707001669, 17402743205, 4568243621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [12923292125, 4333361629, 30086310369, 47249390053], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [86943958063, 10255587401, 43726046505, 34968416553, 13594318121, 25942340029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13040668093, 4350139865, 42954425829, 12889738725], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [86927249459, 39431082281, 34901309737, 5071494441, 21714483629, 13074223533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8628326877, 38659461605, 4299808229], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
  ⟨unpack [74143079479, 35035520325, 26311442757, 4954053957, 17302077897, 8712213961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4841957], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
