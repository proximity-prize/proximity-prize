import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass22
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group22
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23574219783, 40739349519, 87078816799, 53038325819, 43844193595, 35237624123], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43492089147, 8981498275, 21815991743, 13209286079, 13125469631, 4384540155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38727126527, 47300425219, 56020483, 56021507, 34365274639, 12890584591], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36343126027, 57433275415, 87045534763, 10340386887, 35204068671, 30741403967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26345847103, 47753346455, 34868522391, 8880830923, 8780170699, 21664995811], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8780100067, 43122760167, 1099668312555, 4350985723, 1099601202683, 21497221643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [22464011, 22465035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40705795087, 78472104991, 61410089015, 43844193591, 30976211255, 22117980523], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21916660075, 9098938731, 8813654487, 4518755799, 4451648983, 1099685088743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099685089767, 47333910011, 72795647, 1099584424447, 17219033607, 8629104135], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [42955200015, 4300651023, 5685775], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44934049811, 86927957027, 35791351871, 39666736411, 35170583835, 39180413211], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100020634007, 17521027483, 13142179227, 4585868699, 4468424155, 1099735418331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735419355, 25976735199, 13091840479, 1099701865955, 47384244719, 4434801135], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4418091503, 1099550867975, 38660235791, 5683727, 5684751], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44934249495, 78405199911, 31496385599, 35271108911, 30791732527, 30573702447], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4569091479, 8981425579, 8847210923, 8780170667, 1099735418331, 1099735419355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735420379, 1099735421403, 21681769951, 13041509855, 4401314283, 1099668308459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [47367536115, 8629102087, 39238151, 39239175, 34382048779, 4317426187], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53188773915, 86844275759, 1649791051, 31026543891, 30741404947, 22084435219], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43391273383, 30506513831, 8830500263, 8729840039, 17487470007, 8863986103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099802528203, 1099802529227, 1099752198615, 4384538083, 1099701863907, 17269364219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4384535035, 89569787, 1099601198587, 1099601199611, 8629103107, 4300581391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53155353631, 78287964211, 30875617567, 26396174623, 13494502687, 43374564771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26228326819, 4485203379, 1099903192499, 1099903193523, 8947870135, 8796878263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4501979575, 13075062243, 1099701864931, 4418090475, 1099668307435, 1099668308459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099668309483, 42971977227, 22459915, 22460939, 4300647951], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61510541347, 56964127799, 22101138759, 21899883847, 4837526855, 39331258735], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22151465327, 8830432687, 4518756783, 1099919968687, 1099802529227, 1099802530251], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13058286047, 4485132767, 1099685085671, 1099685086695, 156678635, 1099668307435], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8612323851, 4317359627, 5682703], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57249197095, 48441369659, 17755907419, 17554585947, 4736863579, 34985962875], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22034026875, 4552243639, 4485202359, 1099886414263, 1099819306439, 1099819307463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8746543591, 4434867687, 1099685085671, 1099685086695, 1099617975799, 17235808771], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8645879299, 22459915, 22460939, 4300648975], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61393238059, 31395722303, 30808439131, 22067583323, 17621692763, 8880833919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100121297279, 4585796039, 4518754759, 1099819303367, 1099819304391, 1099819305415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819306439, 17319696875, 4451577323, 72792575, 1099584421375, 30070307343], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12890511887, 4300581391, 5682703], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65537213487, 14366917703, 26664535355, 22151536955, 21899884859, 8830433699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099936744875, 1099936745899, 1099936746923, 1099936747947, 13091840479, 4501909983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4418091487, 1099718640095, 72792575, 1099584421375], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69714808883, 26614206755, 26329066787, 9199536419, 8964648363, 8813656491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4501980587, 1099886415287, 1099886416311, 1099718641119, 1099718642143, 4418091491], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099701862883, 21614662127, 8729766383, 56015363, 1099567644163, 4317427207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [5682703], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56930573367, 22168247615, 21916661055, 4854304063, 8863987115, 4552311211], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099936745899, 1099819306439, 1099819307463, 17319697895, 4468355559, 1099668308459], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099668309483, 4367759855, 56015363, 1099567644163, 12907290123, 4317359627], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 22 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group22
