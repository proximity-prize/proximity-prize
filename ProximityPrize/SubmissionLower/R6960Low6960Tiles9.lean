import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass9

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 1006702601, 6325408779, 19261561869, 52850602001, 87026721829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [44396230721, 35520319741, 39497131317, 35084864821, 43423215925, 43775112525], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39430021453, 4600815005, 17502417321, 13173966249, 8845448617, 25958125029], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17334708709, 1099683255787, 1099683322347, 1099683323371, 1099683324395, 4399482353], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649699315, 1099649700339, 8660893177, 25840683521, 38691955209, 12905523725], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8610560525, 20629005, 20630029], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 132 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14697699337, 36039567377, 82630822941, 74209270837, 39715097877, 39463580949], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30571797845, 30420876629, 4835695957, 43406141861, 13140409773, 8811892141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8728009133, 39010507197, 17435303377, 8862216657, 1099783920083, 30303352281], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17418524121, 1099750432219, 1099750433243, 1099700030951, 1099700031975, 1099700032999], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4433034733, 4365927917, 1099582588419, 1099582589443, 8593779217, 3849745], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3850769], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27717805069, 57162809369, 86926194729, 22955019333, 35168680225, 39195286817], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30555096353, 39429882201, 30840088921, 13123634585, 17569521061, 13173895589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13090079141, 1099951691179, 1099951692203, 1099951693227, 1099951694251, 1099767140823], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433035737, 1099750361563, 1099750362587, 43154548193, 21663156709, 8694444525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382703085, 1099599365631, 12939076101, 54181381, 1099565810183, 4332368393], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37403145], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 132 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36174049297, 74091287581, 74075053109, 35369800993, 30940821793, 30722791713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30471207221, 9130662197, 13157185945, 8811891097, 1100018800027, 1099884583355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884584379, 1099884650939, 17452079553, 8878992833, 43271991749, 1099783915987], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783917011, 1099783918035, 4433033693, 1099733582303, 1099733583327, 25891011061], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13006116341, 70957569, 1099582586371, 8644109829, 4332368393], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 132 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44562988053, 82563983397, 44161349697, 31108458765, 35068021005, 39145024781], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13140415845, 13274557829, 13173964165, 8828669317, 43439701401, 1099968469415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968470439, 1099951694247, 21830928825, 13173891513, 1099851025859, 1099851026883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851027907, 4433034701, 1099800692175, 1099800693199, 4449808869, 1099700025831], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649695219, 1099649696243, 8660886017, 4365921793, 30102022665, 20624909], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [42953293329, 17183640081, 12888743441, 1099515552275], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57162942489, 82547408941, 18542612553, 30907269393, 34900320529, 30487987473], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39429949785, 30773047641, 13140411769, 1100052354451, 1100052355475, 1100035579283], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002025875, 13308109205, 13157118357, 8828666261, 1099884580283, 1099884581307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783913939, 1099783914963, 1099783915987, 4483363289, 1099750357467, 1099750358491], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17384968669, 8677664253, 30118867461, 37401097, 37402121, 1099549106699], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12888674833, 8593777169, 1099515551251], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61357380637, 86758559793, 30806610177, 30638977281, 17770926337, 39429952837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545192261, 8962814349, 8878996877, 8778336653, 1100052354451, 1100052355475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018802067, 1099985248659, 13257775541, 8878926261, 1099867802047, 1099867803071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867804095, 1099767135703, 1099767136727, 1099767137751, 1099683247595, 1099683248619], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382697981, 87732733, 38725506561, 21545713153, 12955784705, 1099532329479], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532328463, 57868, 4298810897, 57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61357514785, 73940835381, 30655683861, 26226572565, 9130662165, 35168608585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22283846985, 8895774085, 8795113861, 1100102686087, 1100002023835, 1099968470427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918139803, 13274553765, 8895704485, 8795109797, 1099884579259, 1099884580283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884581307, 1099783914963, 1099750357467, 1099750358491, 1099750359515, 4416253425], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649693171, 1099549106687, 8644107781, 4349143557, 1099532328459, 57864], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34380210701, 21495383565, 57868, 3846673, 1099515550227, 56848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 132 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69796588581, 52583510077, 31007862057, 26511707433, 26276899113, 17569596729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962890041, 1100002023831, 1099968470423, 1099918139799, 1100018795931, 1100018796955], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018797979, 1100018799003, 1100018800027, 8929257893, 8828663205, 1099968463271], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17401744861, 8811815389, 1099716802019, 1099716803043, 1099716804067, 4382699001], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549106683, 1099532328455, 57860, 57864, 30085246477, 1099532327439], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56844, 57868, 3845649, 3846673, 56848, 57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78235596841, 31259739205, 26830338313, 30773122313, 30538315017, 1100236903783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203350375, 1100153019751, 1100119466343, 13173896573, 8828667261, 1100136239487], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17502410165, 8878926261, 1099884578235, 1099884579259, 1099884580283, 4500141509], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834244551, 1099834245575, 1099616138747, 1099616139771, 1099532329467, 4382697981], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [87732733, 1099549105667, 57856, 12939007493, 8627332613, 57860], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25807125001, 57864, 1099532327439, 56844, 57868, 4298810897], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56848, 57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73957475373, 22720138309, 30873715985, 26377495825, 30420877585, 13173965161], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186571123, 1100186572147, 1100136241523, 1100102688115, 1100052357491, 13190669733], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828663205, 1099918131635, 1099918132659, 1099918133683, 1099918134707, 21730264533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13090004437, 1099716802019, 1099716803043, 1099716804067, 4416253425, 1099549106679], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532328451, 57856, 57860, 8627330569, 4332366345, 1099549104651], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56840, 57864, 56844, 57868, 3846673, 56848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78168625201, 5640936525, 30806610177, 26377564417, 21965229313, 1100153015675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153016699, 1100153017723, 1100102687099, 1099951693203, 1099918139795, 8912482709], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811888021, 1100035574167, 17569518005, 8929256885, 1099800690127, 1099800691151], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800692175, 4433031653, 1099700025831, 1099532329463, 1099549105663, 57852], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57856, 57860, 8627332617, 37401097, 37402121, 1099549104651], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56840, 57864, 56844, 57868, 56848, 57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73873726517, 30722792709, 26260126981, 9147439365, 8912551293, 8795113853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136240511, 1100018801039, 1099968470415, 1099934917007, 13308108197, 8912481701], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795109797, 1099918133683, 1099918134707, 1099918135731, 1099800692175, 1099750357467], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750358491, 1099750359515, 4416253429, 121288181, 1099532329463, 1099549105663], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57852, 57856, 57860, 1099549104651, 56840, 57864], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12905520653, 56844, 57868, 56848, 57872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group9
