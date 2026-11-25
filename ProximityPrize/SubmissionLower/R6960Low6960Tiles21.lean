import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass21

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14949288965, 40536579085, 87178495001, 74512373813, 60822078797, 52232290637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39011988893, 357293469, 55973518803], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 124 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 124 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 124 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 124 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36224505865, 65971960853, 87212588077, 14668189769, 52081294697, 34935058793], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60570484107, 51980630409, 51712104905, 34381475309], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 124 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 124 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 124 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 124 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44899116045, 82900504605, 65855332409, 56493625685, 43608803669, 30472385937], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8997557649, 55906477537], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i9 : checks (tilesOf batches) 124 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 124 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 124 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 124 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49194479633, 82883862561, 48776196157, 52198662485, 39313904981, 26059980205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4585150893, 55889703397], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 124 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 124 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 124 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 124 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53405826069, 87095078955, 27418805317, 47954030921, 35052495177, 21597242835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [139255249, 55956815317, 34364695025, 17184835057, 4300003825], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 124 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 124 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 124 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 124 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [65955383321, 87044884531, 1766513741, 43625580869, 34918282567, 5021358405], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [56275519881, 43390763401, 25925760461, 13040865741, 25808317929], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 124 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 124 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 124 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 124 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 124 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61761213469, 82766696499, 39330615625, 30623316299, 5004581193, 56158148005], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38978358693, 21614016977, 13007311315, 21496575469, 8594903537], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 124 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 124 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 124 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 124 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 124 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [74361036833, 57181513787, 52131553637, 39196464485, 26177420671, 4786477437], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17251941857, 8662012385, 34398246377, 21513353705], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 124 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 124 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 124 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 124 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78555409447, 40135931971, 47920475473, 35002162513, 21748236711, 4618705317], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17218388457, 8628458987, 34381471213], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 124 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87028037675, 18862492743, 47987652921, 30791084345, 22117337403, 13007309269], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4400601561, 25808316905, 12923422185, 47266298349], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 124 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [86977709103, 6078257227, 43726243121, 30757531955, 13644845363, 25875427803], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [12973755867, 42971334125, 8594902513], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 124 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82699587635, 39397724473, 30656870715, 5071690041, 21647571401, 8762675657], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38676435437], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 124 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69932194871, 34985385305, 26278084955, 642506073, 17302274517, 8695567831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34364694001, 8594970097], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 124 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤124) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 21 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group21
