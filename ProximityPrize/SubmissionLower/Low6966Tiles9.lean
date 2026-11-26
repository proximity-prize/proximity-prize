import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass9
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2214661125, 1040257035, 6358963211, 23254539277, 61340005397, 87060344873], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [27384202309, 35503608069, 43875775801, 39547461945, 35101641025, 39161802049], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17519259069, 13157188029, 8761561545, 1099834318283, 25907792373, 17317930485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382773749, 1099649767927, 4382704129, 4349151745, 37474829, 1099549103631], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38675178001, 8610560529, 20630033, 20696593], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14731253769, 31996258321, 82647533593, 74226047029, 39731808533, 35336384789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47835550997, 26193085785, 21931595173, 17519193509, 13190742437, 8728007105], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867872707, 43271920069, 43171399137, 1099716809191, 1099716875751, 1099716876775], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416258545, 1099666475507, 1099666476531, 12989410809, 4416257529, 34447389185], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20629009, 42953218581, 21478675989, 8593780245, 4298816021], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27768136717, 53002059801, 86959748137, 23005349957, 35219010857, 34984204585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833284393, 43590697337, 34950573433, 13190741405, 8761560501, 1099918137783], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918204343, 17535965633, 13173960129, 1099733585379, 1099733586403, 1099733652963], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433034729, 1099700028907, 1099700029931, 43120993773, 21579272697, 34413833737], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644111881, 4332370441, 37405197, 38658396693, 17183642133, 3848725], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3849749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36224380945, 82597336093, 61307593785, 39664768269, 35235790093, 35017761037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21864564053, 1100320791895, 13308109229, 8979657133, 13090078125, 1099918134711], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918135735, 1099918136759, 1099918137783, 43238437329, 25991675361, 17368193505], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433034721, 1099733583331, 1099733584355, 34447318529, 70958597, 1099582587399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332368397, 37403149, 17200486929, 4298812949], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48757292053, 82614381605, 35688856641, 31108525337, 30857006361, 39128247577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43573919105, 34917017985, 8828671361, 13291335053, 13173964173, 13073304973], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884580287, 1099884581311, 1099884582335, 1099884583359, 1099884649919, 4449811925], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783914967, 1099783915991, 21696712153, 13090072025, 4416255473, 1099616140799], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616141823, 30118799881, 8627332621, 4332368397, 17200418321, 8610554385], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20625937, 21478607381], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53002192921, 86825597997, 14331531337, 31007931661, 30756347149, 34816507149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43557210489, 26427749753, 13224295805, 13106859389, 1099985247655, 13274553781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8929324469, 8811887029, 1099918134711, 1099918135735, 1099918136759, 1099918137783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800692179, 1099800693203, 1099683248623, 1099683249647, 1099683250671, 17334637041], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349144585, 54179337, 42986916365, 8593778197], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61390935069, 78269288497, 1513741389, 30789898521, 30571868441, 13459181849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39446730061, 26545192269, 13173895573, 8845443477, 1100052352407, 1099985244583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985245607, 1099985246631, 1099901427131, 13207443913, 8878991817, 1099783913943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783914967, 1099783915991, 4449809885, 1099750358495, 70956549, 1099582585351], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25823903241, 38691952141, 4315589137, 20623889], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69830008865, 61173376057, 35336380717, 26595525933, 26343940397, 21898050869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9063552309, 8828665245, 1100018796959, 1100018797983, 1100018799007, 1099968468395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968469419, 1099968535979, 13190668729, 8845439417, 1099767135707, 1099767136731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767137755, 21612824053, 13022961141, 4382700025, 1099632916987, 4365921797], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20624913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74058001445, 44111017021, 31091748129, 26595593505, 30571866401, 17468934485], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100270460247, 13207447965, 8862218653, 1100018795935, 1100018796959, 1100018797983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018799007, 1100018800031, 1100018801055, 1099733580259, 1099733581283, 1099733582307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368190441, 8778326505, 4466585069, 4382701037, 70956549, 1099549105679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65552021545, 39816050753, 26696186169, 26411046201, 21965156665, 13207521625], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287236443, 1100253683035, 1099968465323, 1099968466347, 1099968467371, 1099968468395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8878993841, 4533697969, 1099934909875, 17418524117, 8828660181, 1099683249647], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683250671, 121288185, 1099632916987, 1099532328463, 17200485905, 4315589137], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20623889, 1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69746394157, 22787246149, 26645857573, 22166413605, 26193017125, 1100136240515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119464323, 1100069133699, 13140408717, 1100085905807, 1100085906831, 1100085907855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895701453, 8811883981, 4466588109, 1099817468367, 1099817469391, 21596046841], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13006183929, 1099632916987, 1099632918011, 4365921797, 70956549, 1099549105675], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940766769, 5724821577, 30823452945, 26344010001, 17703816465, 1100069129619], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069130643, 1100069131667, 8962879901, 8828665245, 1100018796959, 1099985246627], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934916003, 17502409161, 8895702473, 1099767135707, 1099767136731, 1099767137755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382700025, 1099632916987, 1099549105675, 20623889, 20624913, 8593778197], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65418009653, 1446632525, 26411048229, 26193017125, 9097106725, 8946104717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811890061, 1100085907855, 1100002022819, 1099985246627, 1099951758763, 13240999361], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8878992833, 1099851023815, 1099851024839, 1099851025863, 1099716803047, 1099716804071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716805095, 4349144585, 54179337, 1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56861632569, 26293676337, 17636705585, 4785363249, 1100002018723, 1100002019747], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002020771, 1100002021795, 1100002022819, 1099951692203, 1099951758763, 8962812337], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845440433, 4500144561, 1099716805095, 4382701041, 1099666472435, 54179337], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099565808139, 4332366349, 4315591181, 3846677, 1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group9
