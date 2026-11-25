import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass14

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1023479817, 10620572683, 27734515725, 82647399445, 87110945841], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35570585859, 39815626001, 35504153873, 43725130001, 30588712277, 9248167253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26109118925, 17502479821, 13090077141, 8778402261, 43221661157, 1099716875767], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716876791, 1099716877815, 138136069, 1099649764871, 1099649765895, 8677734921], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365993481, 12922299933, 8627402269, 37471773, 25790417441, 20693537], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [38658249253, 34363500069], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 137 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 137 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 137 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19093592073, 36257934353, 86942699549, 61441877049, 39681544473, 39480424729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39312793881, 17569597813, 1100253748599, 17552810425, 13173962169, 13090145721], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38993730005, 1099851093463, 1099851094487, 38977028569, 30320196065, 17468922337], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416325101, 1099750428143, 1099750429167, 4449809921, 4399545857, 1099616208399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616209423, 34447387153, 8644111893, 37469725, 37470749, 21495451169], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4298812965], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 137 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 137 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 137 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27969659917, 57213206553, 86959814697, 18760780869, 35168680233, 34984271145], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588715305, 39463436645, 30873708901, 13106856361, 17519254977, 8912548289], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811888065, 1099934978499, 1099934979523, 1099934980547, 1099934981571, 1099800758755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800759779, 21696711149, 4399545849, 1099700094459, 4365922833, 87800337], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660886037, 4365921813, 71024149, 1099582652951, 42986776093, 21478672933], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3913253], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 137 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 137 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 137 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36308398097, 74158527517, 69864037429, 35386643761, 30907267377, 34933938481], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30420942153, 1100438297931, 13123632545, 8811957665, 1100069198243, 13308107197], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979655101, 8862217661, 1099834314203, 1099834315227, 1099834316251, 1099817533919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817534943, 1099817535967, 43221660133, 25941342717, 17317926397, 154842625], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [154909185, 1099666537987, 4332366365, 37401117, 12905518625, 4298810917], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 137 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 137 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 137 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48824531989, 82631224357, 35705699393, 31074970909, 35034533149, 30639042845], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13090148741, 39278951825, 30689158545, 13157183913, 8795111849, 1100035640747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968532923, 1099968533947, 1099968534971, 1099968535995, 17603071425, 13207511489], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817533919, 1099817534943, 1099817535967, 4449808877, 1099750357487, 1099750424047], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17267525137, 8677663249, 4349144593, 71022101, 20622881, 20623905], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48858286105, 86842374185, 18626563141, 31041485069, 30806743309, 30622267661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13140408725, 8828733845, 39228688797, 30571786653, 1100069197219, 1100069198243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069199267, 13257775553, 8912546241, 4584027585, 1099867867603, 1099867868627], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867869651, 1099851021783, 1099851088343, 1099851089367, 17334702585, 1099632915979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632982539, 4382698001, 87732753, 25823900185, 17234038297, 4332365341], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8610554401], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57247093789, 86792178737, 35084864777, 30638977289, 13526290697, 35118273905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478147953, 13190738325, 8828666261, 1100119526807, 1100052418983, 1100052420007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052421031, 1100035644839, 13341660601, 8979654073, 1099867865555, 1099867866579], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867867603, 4483363297, 1099800689123, 1099800755683, 87732753, 1099599427091], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349142553, 54177305, 25807125021, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61441531937, 69729819701, 26411113769, 26226637097, 9130726697, 35118276957], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22250292573, 8878995865, 1100102682011, 1100102748571, 1100102749595, 1100102750619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018865583, 1100018866607, 1099968535983, 13207510469, 8828661189, 1099800689123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800755683, 1099800756707, 4382699009, 1099666470403, 34430542357, 8660885013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349143573, 17233970713, 8644106777, 1099565806107, 56860, 56864], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3844645, 3845669, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74074844197, 44127859773, 31091813669, 26562039077, 26327230757, 17468933465], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100354410843, 1100304080219, 1100069127587, 1100069194147, 1100069195171, 1100069196195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069197219, 8979655085, 8828663213, 1100018794927, 17435299301, 8845435365], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767133675, 1099767134699, 1099767201259, 104508941, 1099616137743, 56856], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30102089245, 56860, 56864, 17183706661, 4298809893, 3844645], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041358377, 31326847041, 26796849441, 26528552225, 26293743905, 13106924913], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203416947, 8929325473, 8795110817, 1100069194147, 1100035640747, 1100035641771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035642795, 1100002089387, 1099851021783, 1099851088343, 1099851089367, 13207442905], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8845436377, 205173237, 1099716802039, 1099716803063, 25823902233, 4349142553], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54177305, 56856, 56860, 55840, 56864, 55844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763236909, 22804088901, 26662700329, 26377560361, 26176306473, 1100153084295], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102753671, 8878996877, 8795179405, 1100153083279, 9029984701, 8862215613], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4516919741, 1099934976451, 1099934977475, 1099934978499, 1099851088343, 1099851089367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716803063, 1099716869623, 21629601281, 8744771073, 4399476225, 1099666470403], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56852, 56856, 37400093, 37401117, 56860, 55840], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56864, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957609521, 5741664329, 30789898517, 30538314005, 13408850197, 13241069961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8862220681, 1100169858443, 1100119527831, 1100119528855, 1100018866599, 1099968535975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535963589, 8946099653, 1099884642767, 1099884643791, 1099884644815, 4483363297], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800689123, 1099800755683, 87732753, 1099599427091, 56852, 56856], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17217262109, 4332365341, 37400093, 56860, 55840, 56864], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69679488053, 30689303837, 21998779677, 9113883933, 8811888029, 1100085971359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085972383, 1100085973407, 1100085974431, 1100052421023, 1100002090399, 13308173749], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912547253, 4567251381, 1099851088343, 1099851089367, 1099700091387, 1099700092411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399476229, 1099649693191, 56852, 56856, 8627330589, 4332366365], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56860, 20623905, 55840, 56864, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 14 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group14
