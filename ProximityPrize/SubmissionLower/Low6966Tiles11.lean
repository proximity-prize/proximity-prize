import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass11
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 1057034251, 10435957771, 27717672973, 86891969557, 78588055601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39899446533, 39731946757, 52231113989, 35520188683, 26226573669, 22015413677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21864490413, 17502485933, 8744784341, 43271927265, 4500143613, 4433036797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716808191, 1099716809215, 1099716810239, 1099716811263, 34514429449, 25907792393], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13022897677, 8711222797, 38708515363, 54183457, 1099565812259, 21478607405], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4298815021], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15184435209, 32096987153, 86925789209, 65736776757, 39798917393, 39581020433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43624470801, 21881341297, 17653406133, 13274557877, 13173964213, 8711228885], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884583383, 30320128497, 17435300337, 1099750362615, 1099750363639, 1099750364663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43171260921, 4433034749, 1099716806143, 1099716807167, 8694443541, 4365924885], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565810211, 38691886629, 8610555433, 20625961, 20626985], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27936039949, 57246760985, 86976526377, 14532856901, 31007930669, 35000981805], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588648749, 39463436653, 30873643373, 13157186989, 17535965641, 13140340169], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901357523, 1099901358547, 1099901359571, 1099901360595, 4433034737, 1099767137779], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767138803, 8694443529, 154843657, 21596047889, 43053819413, 1099616140823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616141847, 8644043297, 4332367397, 37402149], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36308332561, 74158461981, 65619336245, 35403355441, 30957599025, 30722791729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21931604309, 9113882965, 8828664261, 8728004037, 13274552785, 8895703505], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811886033, 1099884581335, 1099884582359, 1099884583383, 43255149029, 1099800692203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800693227, 1099800694251, 1099700027907, 25924499977, 13039670793, 154842633], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666471435, 1099666472459, 4365920797, 4332368413, 20623913, 34363432493], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44663716885, 82631157797, 35722410049, 31125235997, 30873717021, 34917165341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13106859401, 13257779621, 13140408741, 8795113893, 39178288561, 30588495281], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968468419, 1099968469443, 1099867802075, 1099867803099, 1099867804123, 17502341601], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13140336097, 4449810917, 1099817468391, 1099817469415, 4466585089, 4382701057], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649695247, 1099599361563, 1099599362587, 21545715229, 8644042273, 4349143585], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3846701], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53069367321, 86842375213, 10137227337, 31024708881, 30773124369, 30588648721], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39346063753, 26461303177, 13173964177, 8811892113, 13274553789, 8895704509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811887037, 1099985246655, 1099934911947, 1099934912971, 1099934913995, 1099867801051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867802075, 1099750357495, 1099750358519, 1099750359543, 17401744889, 4416253449], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666470411, 4365853213, 4365920797, 20623913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57247028253, 82547477553, 30840163605, 26427895061, 17770858773, 35151762801], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494859633, 1100085905831, 1100085906855, 1100085907879, 1100085908903, 1100069132711], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912481717, 8828664245, 1100018795959, 13274551761, 8895702481, 1099767134707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767135731, 1099767136755, 171618821, 1099683247623, 4365854237, 70954525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21528869409, 12939006497, 1099515550255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69880406049, 56945517625, 31091679545, 26629079353, 26360716601, 21898049861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9063551301, 8845441453, 1100052350383, 1100052351407, 1100052352431, 1100002021819], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002022843, 1099968469435, 13207444937, 4634291657, 4567250377, 1099783912943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783913967, 21629534729, 8744704521, 1099649693199, 1099649694223, 4382631449], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [70954525, 70955549, 1099532327467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69846920229, 44161347645, 31041416501, 26545261877, 26293676341, 13257852257], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100371121507, 1100320790883, 8946035125, 8811820469, 1100018794935, 1099985241535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985242559, 1099985243583, 1099985244607, 1099783910895, 1099783911919, 1099783912943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17435299313, 8811815409, 4382699021, 30118800929, 37400101, 37401125], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532327463, 4315521577, 4315589161, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041292841, 27132543041, 26813561121, 26545263905, 26310455585, 1100203347339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203348363, 1100186572171, 1100136241547, 8912482725, 8828665253, 1100085905831], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13224220125, 8845370845, 1099834244579, 1099834245603, 1099834246627, 4433031669], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750357495, 87732761, 1099599361563, 25840613917, 4365854237, 70954525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549104675, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74007807021, 14331530309, 30890493213, 26394273053, 26193019165, 8912552325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102684067, 1100102685091, 1100069131683, 1100018801059, 9013142965, 8862151093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761556405, 1099884579287, 1099834244579, 1099834245603, 1099834246627, 21746976229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8895700453, 4416254457, 1099733580283, 87732761, 1099599361563, 4365920797], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549104671, 21495383593, 54824, 55848, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957543985, 1530517577, 30840230165, 26360787221, 13475958037, 8929259941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828665253, 1100085905831, 1100085906855, 1100085907879, 1100052354471, 1099918137787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535963601, 8895702481, 1099834244579, 1099834245603, 1099834246627, 4433031673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733580283, 4365854237, 4332367389, 1099582584351, 1099549104671, 12905452073], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315521577, 20622889, 20623913, 54824, 55848, 54828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65434786869, 26427825449, 26209794345, 4886025513, 8895707541, 8811890069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153016727, 1099968468411, 1099918137787, 13240999369, 8828595657, 1099918132687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918133711, 1099918134735, 1099834243555, 1099834244579, 1099834245603, 4433030661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683247623, 1099549104671, 8644042273, 4349143585, 20623913, 54824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55848, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52667394105, 22015486281, 17569530185, 4751807817, 8778334633, 1100069129643], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069130667, 1099968468411, 1099918137787, 8878926285, 4567250381, 1099918130639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867800027, 1099867801051, 1099867802075, 1099632915987, 1099632917011, 4399475221], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [104509973, 1099549104671, 54824, 55848, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 11 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6966Allocation.Group11
