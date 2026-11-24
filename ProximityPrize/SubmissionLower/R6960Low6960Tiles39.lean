import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass39

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group39
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23676521477, 23642973199, 32200604695, 36446297123, 23511072815, 10592622647], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6280881211, 1969138751, 1969139775, 1935586367, 1885255747, 1851702339], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1818148931, 1767818311, 1734264903, 1717488711, 1667158091, 1099752722907], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719167459, 1099702389223, 1099668833775, 1099635278327, 1099601722879, 1099568167431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099534611983], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 132 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 132 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 132 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27954714635, 32200602647, 36463072287, 23527847979, 14904365107, 6280880187], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1985914939, 1952361535, 1902030911, 1868477503, 1818146883, 1784593475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1751040067, 1700709447, 1667156039, 1633602631, 1583272011, 1099836608967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099803053519, 1099769498071, 1099735942623, 1099702387175, 1099668831727, 1099635276279], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099601720831, 1099568165383, 6204944], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 132 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 132 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 132 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23642973199, 27905637399, 36446296099, 19216104495, 10609397811, 6297656375], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1985913915, 1969137723, 1902029887, 1851699263, 1818145855, 1751038019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1717484611, 1683931203, 1633600583, 1600047175, 1566493767, 1532940363], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099886940603, 1099870162367, 1099836606919, 1099803051471, 1099769496023, 1099735940575], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099702385127, 1099652052467, 1099618497019, 1099568164359, 6203920], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 132 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 132 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 132 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [19331231763, 27888862235, 32151330851, 19216105519, 6297654327, 6297656375], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1985913915, 1935583291, 1868475455, 1818144831, 1767814207, 1717483587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1683930179, 1633599555, 1583268935, 1549715527, 1516162119, 1465831499], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099954049451, 1099920494003, 1099886938555, 1099853383107, 1099819827659, 1099769494999], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099735939551, 1099702384103, 1099652051443, 1099601718783, 1099551386123], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 132 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 132 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 132 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [32200604695, 32151329827, 19216104495, 10609397811, 2002689079, 1985912891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1969136699, 1918806075, 1834921023, 1801367615, 1751036991, 1683929155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1650375747, 1600045123, 1549714503, 1516161095, 1482607687, 1432277067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099987603875, 1099954048427, 1099920492979, 1099886937531, 1099853382083, 1099803049423], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099769493975, 1099719161315, 1099668828655, 1099635273207, 1099568163335, 6202896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [27888863259, 32134554663, 14921139247, 6297654327, 2002689079, 1985912891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1952359483, 1902028859, 1834921023, 1784590399, 1734259775, 1667151939], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1616821315, 1583267907, 1516160071, 1482606663, 1449053255, 1398722635], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100021158299, 1099987602851, 1099954047403, 1099920491955, 1099870159295, 1099836603847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099786271187, 1099735938527, 1099685605867, 1099635273207, 1099584940547, 1099534607887], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [36463072287, 23527847979, 10609397811, 2002689079, 1985912891, 1952359483], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1902028859, 1818143807, 1767813183, 1717482559, 1650374723, 1600044099], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1566490691, 1499382855, 1465829447, 1432276039, 1365168203, 1100054712723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100004380063, 1099970824615, 1099937269167, 1099886936507, 1099853381059, 1099803048399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099752715739, 1099702383079, 1099652050419, 1099584940547, 1099534607887], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [32151330851, 19216105519, 6297654327, 2002689079, 1985912891, 1969136699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1902028859, 1834921023, 1767813183, 1717482559, 1650374723, 1600044099], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1549713475, 1499382855, 1449052231, 1415498823, 1348390987, 1100071489935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100021157275, 1099987601827, 1099937269167, 1099903713719, 1099853381059, 1099803048399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099752715739, 1099702383079, 1099635273207, 1099584940547, 6202896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27839589415, 14904363059, 6297655351, 1985912891, 1985913915, 1918806075], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1834921023, 1784590399, 1717482559, 1650374723, 1600044099, 1549713475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482605639, 1449052231, 1398721607, 1348390987, 1100071489935, 1100037934487], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099987601827, 1099954046379, 1099903713719, 1099853381059, 1099803048399, 1099752715739], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099685605867, 1099635273207, 1099568163335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23527847979, 10609397811, 6297656375, 1985913915, 1935583291, 1851698239], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1784590399, 1734259775, 1650374723, 1600044099, 1549713475, 1482605639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1449052231, 1398721607, 1348390987, 1100071489935, 1100037934487, 1099987601827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099954046379, 1099903713719, 1099853381059, 1099803048399, 1099735938527, 1099685605867], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099618495995, 1099551386123], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19216106543, 6297655351, 1985912891, 1985913915, 1952360507, 1868475455], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1801367615, 1751036991, 1667151939, 1616821315, 1566490691, 1499382855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1449052231, 1398721607, 1331613771, 1100088267147, 1100037934487, 1099987601827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937269167, 1099886936507, 1099836603847, 1099786271187, 1099719161315, 1099668828655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099601718783, 1099534608911], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14904365107, 6280880187, 1969137723, 1885252671, 1818144831, 1751036991], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1683929155, 1616821315, 1566490691, 1499382855, 1449052231, 1398721607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1348390987, 1100071489935, 1100037934487, 1099987601827, 1099937269167, 1099886936507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099836603847, 1099769493975, 1099719161315, 1099652051443, 1099584941571, 6203920], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((39 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 39 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group39
