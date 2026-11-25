import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass29

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group29
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27922861063, 40658282515, 86947090463, 44299691067, 35340439835, 30894617883], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39165859099, 13127695743, 1100106747263, 13295392151, 13161178519, 8849503639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099855086011, 1099855087035, 1099855088059, 1099737642455, 1099737643479, 1099737644503], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4470646235, 4403539419, 21650437603, 13060509155, 38763047411, 1099603422711], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099603423735, 4369980923, 34384269831, 24684039, 24685063, 34367344139], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36429895691, 57267993623, 86880121899, 5846386759, 30877840663, 39132304663], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17758207255, 39316634991, 30659732847, 13328946571, 13177955723, 8849503627], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099955749283, 1099955750307, 1099855088059, 1099855089083, 1099787974091, 1099787975115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099787976139, 4487423443, 1099754417619, 1099754418643, 17355474395, 4386691575], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4369981943, 38729423355, 25827894783, 17238032895, 41462275, 8614548999], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [7905803, 7906827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40674927631, 69867818015, 65506021427, 35273329971, 26599649587, 26364841267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21918886199, 13329023287, 8832723363, 8732063139, 1099955749283, 1099955750307], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099955751331, 1099955752355, 13161172419, 4588019139, 4537755075, 1099804751303], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099804752327, 1099804753351, 1099704085983, 1099704087007, 38762980851, 21549773307], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12959844859, 58238463, 1099569867263, 4319582727, 7905803], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40759078931, 65606473763, 56916088887, 22002768187, 26079703355, 1100391959867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35139180863, 26431880511, 8849502599, 1100073188743, 1100073189767, 1100073190791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100073191815, 8866208187, 8765613499, 1099804750279, 1099804751303, 1099804752327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17372249567, 8782320095, 158901735, 1099670530535, 1099670531559, 30139636219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21549775355, 4353203711, 42957353483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44836076567, 78256564263, 27052717119, 31028766987, 26549389579, 30542374155], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100157076851, 1100157077875, 1100157078899, 8983651711, 8883057023, 1100106743167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100106744191, 13177948615, 8815876551, 1099804750279, 1099804751303, 1099804752327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38863715803, 30257079771, 4420314591, 1099704085983, 12993398259, 4353137151], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4336427519, 1099569867263, 25777563147, 17187701259, 7905803, 7906827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48946628635, 73961666603, 14251704387, 26700314895, 26415174927, 26197078287], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8916611447, 8799174007, 1100056414603, 1100056415627, 13194728875, 8799102379], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099922193835, 1099922194859, 1099922195883, 39031490995, 26129887667, 1099804750279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099804751303, 1099804752327, 4420314591, 1099704085983, 13010177519, 4386758135], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [58238463, 58239487, 25777631755], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53057115167, 65405356083, 5745723463, 26499057951, 22002771231, 17607212319], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100073188743, 1100073189767, 1100073190791, 34904298891, 22019471755, 8866211231], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4554535327, 1099972524447, 1099955751331, 1099955752355, 13127619023, 4537688527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099704087007, 1099704088031, 175679971, 1099687308771, 8597770763, 4302872075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [7906827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53006852131, 61076837431, 26398397723, 21918888219, 4856531227, 34937921923], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21985985923, 8866279815, 1100073188743, 1100073189767, 1100073190791, 1099955751331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099955752355, 8916540851, 4604864947, 1099787973067, 1099787974091, 1099787975115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17238033919, 8648104447, 58239487, 1099569868287, 4319651331, 7906827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61345197095, 39803398203, 30877838667, 22136982859, 17640695115, 13228357967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100308072783, 1100308073807, 1099955747235, 1099955748259, 1099955749283, 1099955750307], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8832722363, 4470649275, 1099670532583, 1099670533607, 13026954731, 8715214315], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [91793911, 91794935, 8597839371], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65489172523, 22757750851, 26717092139, 22187316523, 17707805995, 1100140298615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100140299639, 1100140300663, 1100140301687, 8815947179, 1099922192811, 1099922193835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13110842839, 4520977879, 4386762211, 1099687310819, 75017723, 1099586646523], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65438909487, 9990292551, 26616431907, 22086656291, 17657542947, 4554537367], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100006080919, 1100006081943, 1100006082967, 1100006083991, 8933319095, 4604865975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4487427511, 1099737644503, 1099670533607, 1099670534631, 21600110063, 8715214319], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [41463299, 41464323, 4302875147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61127168051, 1534643271, 22338310435, 22019549475, 13362577699, 1100006080919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100006081943, 1100006082967, 8933386663, 4571313575, 1099938971047, 1099871866295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099653756395, 1099653757419, 17288368627, 8681727475, 75018747, 4302874123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [7908875], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52621188151, 22086655291, 17623987515, 4772645179, 4588090791, 1099938971047], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099938972071, 1099938973095, 1099905419695, 1099905420719, 13110844879, 4554534351], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099636979183, 1099636980207, 12909583879], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 29 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group29
