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
  ⟨unpack [2248215557, 2063732745, 14798296075, 32113763341, 86976185369, 74326841397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43993351453, 39631548701, 26428021105, 26277098865, 13408981361, 38960305621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13073429997, 8728135149, 4433236465, 4382906865, 38809309689, 47399386617], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34447520265, 25857660425, 1099599567371, 1099599568395, 12939211281, 4349347345], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332572177, 1099549234711, 38675377689, 8593981981, 4050461, 4051485], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 135 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 135 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 135 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19295049737, 36341951505, 78503890973, 69998320693, 39597855037, 35185588541], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588771689, 30437850473, 1100270656875, 13123763653, 8812088773, 4500347333], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17401945577, 13056651753, 43154681325, 1099666676219, 1099649895935, 1099649896959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649897983, 4399612417, 4366125569, 43054012933, 30169332229, 21579471365], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8627466773, 4332502549, 37603861, 4048413], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 135 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 135 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 135 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32080208909, 57297290265, 86976724013, 14499434569, 30957731121, 35001179441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588846385, 43607606649, 30756401529, 13123764657, 17485766093, 8912679373], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812019149, 4466790861, 1099851225551, 1099851226575, 4399679981, 43137902065], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666674171, 1099666675195, 4366056965, 104711685, 17267659273, 1099599563275], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599564299, 38675304985, 12905653785, 20758041, 20824601, 4298946077], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 135 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 135 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 135 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36409192465, 74175370269, 69880880181, 39597856053, 30924176693, 26394467661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26243545421, 9130792269, 8862349761, 8761689537, 1099901555139, 1099834447315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834448339, 1099834449363, 17385168357, 8778461669, 1099716937199, 1099717003759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717004783, 43087573501, 25874365957, 17284504069, 104644101, 1099616272903], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332499477, 37534229, 38675308057, 8610688537], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 135 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 135 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 135 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44747799573, 82648066085, 40000796737, 35336513825, 35068218657, 30639108385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13106991493, 13190869421, 8828797357, 8744914349, 1099918334399, 1099918335423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43322457541, 21797506509, 13174089165, 1099817668055, 1099817669079, 1099817670103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733713387, 1099733714411, 1099733780971, 4416386553, 1099666603515, 30135708173], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21545847309, 8627463701, 4332499477, 20757017, 12888875549], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53086275609, 86859283501, 14381994057, 31024839957, 30790098197, 34850258197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43523787149, 30639027597, 13190872461, 8845577613, 1099968666035, 1099968667059], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13257907653, 8912678341, 4584159685, 1099851222479, 1099851223503, 1099851224527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800822235, 1099800823259, 1099800824283, 17301214717, 71088653, 1099582717455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332498453, 37533205, 42970270233, 30085445145, 17183839773], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [69897180189, 74024851509, 30689368361, 26293877033, 9181123881, 39581078841], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26696318265, 8879126953, 8761689513, 1100002218411, 1099935110587, 1099935111611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935112635, 13274683841, 8963008961, 8828794305, 1099817600471, 1099817601495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817668055, 1099700158963, 4366054909, 1099649826303, 54310417, 1099565939219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38675306009, 25790479897, 4298943005, 3977757], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61458374689, 69746662453, 30672657709, 26226769197, 4886157613, 35151962465], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26461504865, 8879127965, 8761690525, 1100052551071, 1099918334399, 1099918335423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207577025, 8862347713, 1099867933131, 1099867999691, 1099868000715, 1099750489575], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750490599, 1099750491623, 4382831109, 1099616270855, 21562623497, 12972760585], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349275665, 3978781], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69880671269, 48406114365, 35219139901, 26478285117, 22032395581, 17536173397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100354476375, 1100354542935, 1099985372591, 1099985373615, 1099985374639, 1099985441199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985442223, 8879123909, 4550605253, 1099884708295, 17401876969, 8812013033], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616270855, 1099616271879, 30135709197, 17250881037, 4349276685, 3977757], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3978781], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78319679529, 27099120709, 31041616157, 26528618781, 26310587677, 1100153147783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153148807, 1100153215367, 1100153216391, 8946234785, 8812020129, 1100035706275], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190797781, 8879122901, 1099800822235, 1099800823259, 1099800824283, 4382832121], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666603515, 25857587721, 17267725833, 54310417, 1099565939219, 4298943005], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3977757], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74041558061, 18559519813, 30907467045, 26411246885, 26209992997, 8879128977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102815123, 1100102816147, 1100102882707, 1100102883731, 1100102884755, 13207643585], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812017089, 1099800822235, 1099800823259, 1099800824283, 21663286769, 13073423857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382832121, 1099666603515, 4349275665, 54310417, 1099565939219], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78235930673, 1530715213, 30873915665, 30605553937, 13476090129, 13241201045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8862351765, 1100086037911, 1100035707299, 1100035773859, 1100035774883, 1099918335423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17485763029, 13123757525, 1099800822235, 1099800823259, 1099800824283, 4433163757], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716935151, 8644240913, 4332499473, 1099565939219, 3977757, 3978781], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65451695157, 1530715213, 30672657709, 21982133549, 9097237805, 8828796329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002150827, 1100002151851, 1100002218411, 1100002219435, 1100002220459, 1099918335423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13274684865, 8929455553, 8778463681, 1099750491623, 188529137, 1099700157939], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700158963, 4332498453, 37533205], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group16
