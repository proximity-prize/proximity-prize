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
  ⟨unpack [27971423239, 45052405779, 82919183391, 48828228667, 43727738203, 35104391515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21833688503, 17471684023, 392483255, 8680422911, 4385458687, 47284496907], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34383036943, 21498209807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
  ⟨unpack [40639404043, 61695803419, 87063362607, 1868877899, 35154722119, 34919915847], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13579371847, 47787819411, 34903060883, 17471611343, 13143160271, 43140454887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4435789295, 4368682479, 1099585342979, 21531694599, 1099551789579, 8613312015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4318347791, 6605331], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [45002007567, 61679226911, 74212084787, 26548079955, 30541064531, 9217296723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43492921747, 30608096659, 13210266055, 8864971207, 8764310983, 1099686007275], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [140822003, 1099652450803, 1099652451827, 47351604731, 4335122955, 40157707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17203174927], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [45086158867, 74245430307, 48593347643, 39499947339, 30792648011, 21900797311], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17522015615, 1100138991999, 4519673299, 4435789267, 1099786669523, 13076047335], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8730752487, 1099635672567, 1099635673591, 25876989435, 12992160251, 4335121931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [40156683, 40157707, 47250944531], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [45086358551, 74195167271, 35775557695, 35238537539, 26564857155, 26296428867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13109609875, 13176711619, 8797862339, 1099820221899, 1099820222923, 1099820223947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820224971, 4385454583, 1099635671543, 21548469763, 12958606851, 4335121931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23379471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [45052938267, 78372762667, 18696355907, 35255383339, 26514528555, 26296497451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8915301803, 8781087151, 1099937664431, 1099937665455, 17387723231, 8797859295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099736334815, 1099736335839, 1099736336863, 107264507, 1099618893307, 30138398211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17253504515, 42956048915, 8596531731, 6600211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [57417815071, 69782899763, 1667551307, 26615188787, 26313206067, 13445154099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43459368347, 26279641499, 13193488823, 8814639543, 1099887330747, 1099887331771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099887332795, 1099753116123, 4385454575, 1099669225967, 12975316479, 8646864387], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56932871, 1099568561671, 4301565459, 6600211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [61545078819, 56965110839, 22152453447, 17723340103, 9099856199, 39315399031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26397084023, 1099853777347, 1099853778371, 1099853779395, 4586780107, 4469341643], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820221899, 13025715691, 1099635670519, 1099635671543, 21498137103, 12908274191], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4318343695, 6601235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [57283734567, 48442352699, 17790379355, 17589123419, 4754558299, 34970168707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22068564355, 4570003903, 4469342655, 1099870554559, 1099820223947, 1099820224971], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099686003179, 1099686004203, 8747526639, 4435785199, 1099585338883, 17186394643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8596530707, 6600211, 6601235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [61410998315, 31413482559, 35037280607, 22068567391, 13260600707, 8881751427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100122214787, 1099820221899, 1099820222923, 1099820223947, 4502894047, 1099736333791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099736334815, 13042425327, 8730750447, 30138399235, 17253505539, 4301565459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [6600211, 6601235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
  ⟨unpack [65538196527, 14367835207, 30876534075, 22118901051, 17673010491, 1099954442667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4586782131, 1099920885171, 1099920886195, 1099920887219, 13143156183, 4553225687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [107265531, 1099618894331, 25860212223, 12975383039], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
  ⟨unpack [57032216627, 10156820551, 26497749331, 17740049747, 17538793811, 4570005931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099870554559, 1099870555583, 1099870556607, 8831413723, 4486117851, 1099669225967], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099669226991, 21548470787, 8663640579, 40155659, 40156683], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
