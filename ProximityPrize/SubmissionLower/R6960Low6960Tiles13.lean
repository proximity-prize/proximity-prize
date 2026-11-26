import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass13
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23541648391, 40605983759, 86962162719, 48609861691, 43794648351, 35154524447], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34970049823, 13193298307, 17437859251, 13092630963, 4402037199, 1099669031375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099669032399, 30154979807, 17270086111, 43022886371, 8646668775, 4334927335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38694506987, 1099551589867, 8596336115, 6405619, 6406643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i51 : checks (tilesOf batches) 124 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36260091915, 53105540119, 86945656875, 10173334599, 30909821223, 34936492327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26279458087, 43375213967, 34768644495, 8847996323, 8764113315, 17454633395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13126182323, 1099719364035, 1099669029327, 1099669030351, 1099669031375, 43089992147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351702499, 73514467, 8613111279, 4318147055, 30071024115, 21481163251], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6404595], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 124 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40589206543, 69899734047, 65571622963, 39432572219, 30792447291, 26279449927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26111684935, 1100239457607, 13092630939, 8747336091, 17353971139, 8764107203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099719360963, 1099719361987, 1099719363011, 4402034127, 1099669028303, 43039663583], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25809679851, 17219752427, 39957995, 1099551586795, 8613111279, 23179759], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 124 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40673423379, 82583443491, 39919265851, 39533238543, 30842781967, 30624751887], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13142966635, 8982143383, 13109407127, 4536253847, 1099820025259, 1099820026283], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820027307, 21648933323, 13042227659, 4452363727, 157398479, 1099669027279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652251091, 1099652252115, 34433096163, 21548269027, 8596265459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40656845847, 78305322023, 31379730495, 35238339863, 30725343511, 26279454999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8780891515, 8931879315, 8814441875, 1099920687507, 1099820025259, 1099820026283], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820027307, 17437854135, 8847924663, 1099685803467, 1099685804491, 1099685805515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351699431, 56734183, 30104577515, 21514716651], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 124 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 124 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 124 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48877815835, 82499696683, 5760927815, 30960220419, 30691858691, 22001268995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8814442883, 1099987797379, 13226776987, 8881547675, 8764110235, 43274619299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26111604131, 1099836803495, 1099836804519, 1099752915387, 1099702580679, 1099702581703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702582727, 12991893979, 4368476643, 73511395, 8613110255, 42955917811], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 124 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 124 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 124 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 124 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 124 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53021922335, 73926608947, 26547816719, 30540866831, 9183544591, 39130649987], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26195492227, 13193225603, 8847996291, 1099987796355, 1099870356895, 1099870357919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099870358943, 1099719357891, 1099719358915, 1099719359939, 13025450443, 4452362703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [157397455, 21514714603, 12924786155, 4318143983], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 124 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 124 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 124 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 124 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61360267299, 52619615287, 21984484667, 17572148539, 4737583419, 35070566731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22168962379, 4536251803, 1099887132059, 1099887133083, 1099887134107, 1099836803495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099836804519, 8847924663, 8764107191, 1099635471831, 1099635472855, 4368476643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [73511395, 21481162227], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 124 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 124 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 124 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 124 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65537862695, 35557256255, 30876265779, 22168964403, 17739851059, 13159741791], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100138793311, 1100138794335, 4469143971, 1099853578659, 1099853579683, 8797660603], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4452364731, 1099669027279, 1099669028303, 17286860251, 8696996315, 73511395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099585140195, 23178735], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 124 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65487599659, 22773020739, 30842779947, 26313005355, 21833495851, 1100021353851], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8847996291, 1099987796355, 1099987797379, 1099987798403, 13176445359, 8814438831], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099719357891, 1099719358915, 1099719359939, 25826458087, 12941563367, 4351699431], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56734183], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65437336623, 9988785223, 26564592931, 22068371747, 17639258403, 4536252819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099920687507, 1099903911319, 1099903912343, 1099903913367, 8864702899, 4569804211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4452365747, 1099669028303, 1099618694619, 1099618695643, 21548271075, 12958408163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 124 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65387073587, 22269628699, 22018042139, 13377847579, 1099920687507, 1099920688531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099920689555, 1099920690579, 8898324895, 4553029023, 1099870354847, 17286861275], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8696997339, 90289631, 1099601918431, 39956971], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤124) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤136 ∧ 6+a.j≤57 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group13
