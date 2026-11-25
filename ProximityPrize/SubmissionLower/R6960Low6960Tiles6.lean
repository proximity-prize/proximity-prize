import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass6

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 1006702601, 5620634633, 19144055821, 48656298001, 133986082849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39748657389, 56526080237, 30907416813, 31225221373, 43674448229, 35084655973], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26276825493, 21881267605, 13257784725, 8811892153, 4500150713, 1099666479599], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666480623, 4433034737, 4399482353, 1099649699315, 1099649700339, 1099649701363], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25890947573, 12989343225, 4399478265, 20629005, 20630029, 4298743313], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 132 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14546638857, 31878752273, 78352500761, 78437061685, 39698254101, 35286053141], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30672459077, 34766173509, 4919580997, 39161371033, 13173896617, 13090080169], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951691179, 43271995845, 17418524121, 8828594649, 4416259549, 1099733585375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733586399, 1099733588447, 1099733589471, 4433032689, 4399480305, 30185910773], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [121213429, 1099599365631, 1099599366655, 20626957, 20627981, 3698192], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27633853453, 48740581401, 112494604329, 1614404685, 35353096433, 43624404209], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511786225, 39262110081, 30672316801, 17653339541, 17519192469, 8912485781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795113893, 1099968468391, 1099968469415, 26058499533, 1099783921107, 1099750361563], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750362587, 1099750363611, 17384901089, 4399480293, 1099700028903, 8744708585], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4449809897, 70958593, 1099582587395, 12922232329, 4298812945, 20624912], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 132 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36157272081, 65618793501, 78319621173, 34917094697, 26276903209, 9197770025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35252360509, 26595457341, 8845375909, 8778335653, 1099968467367, 13291263409], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190669745, 4617516465, 1099867805119, 1099867806143, 1099867807167, 34698768833], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767137751, 1099767138775, 1099767139799, 1099700026855, 1099700027879, 8660821501], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365922813, 70957569, 25823836677, 4298745361, 4298812945, 3847696], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 132 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44546210837, 82563983397, 39899936833, 31091681549, 35051243789, 17938558221], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13207454061, 13123637613, 43439701397, 1099951690155, 1099951691179, 1099951692203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934916011, 17569450421, 13224222133, 1099867799999, 1099867801023, 1099867802047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867803071, 4583960005, 4500075973, 1099834244551, 104510969, 1099616139771], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30118799877, 8627265033, 4332300809, 42970070541, 20623885, 56848], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i55 : checks (tilesOf batches) 132 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48740714521, 91053389865, 14281199689, 35218946297, 30789901561, 17921850617], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39262177665, 26377417089, 1100018799003, 1100018800027, 1100002023835, 1099968470427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13257776553, 8878927273, 4550408617, 4500144557, 1099934910895, 1099934911919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13190598089, 1099716805091, 1099716806115, 1099683248619, 1099683249643, 4382633457], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649693171, 8644042245, 4349078021, 37401097, 56840, 56844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833040], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57146299421, 78218890289, 5741598793, 30773054733, 30571801869, 9231256845], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35134985561, 26494859609, 13207448969, 8845376905, 1100085905803, 1099934914983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884584359, 1099951689131, 1099951690155, 1099951691179, 13240931769, 8895702457], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817467339, 1099817468363, 1099817469387, 4416188889, 1099750357467, 1099616072187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616138747, 56832, 4349076997, 54111749, 56836, 21512092169], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12922229257, 56840, 16833036, 3777040, 16833040], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57129656353, 69662578741, 1429855309, 30655682841, 26226571545, 4902802713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35084722521, 17955259737, 8862153097, 8795112841, 1100085907851, 1099867807143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13257709993, 8895703465, 1099951617451, 1099918136751, 1099867806127, 1099867801023], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867802047, 1099867803071, 1099800623567, 1099800690127, 1099800691151, 4399409653], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632849399, 56828, 56832, 8644041221, 4349076997, 16833028], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34396987913, 16833032, 16833036, 3845648, 33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57113013285, 61106267193, 26276832549, 26109133093, 1100387900711, 30789758297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22099299673, 8845377913, 1100153015675, 1100153016699, 1100119463291, 1100069132667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979588513, 8845373857, 1099985173923, 1099884577211, 1099884578235, 1099884579259], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716735459, 1099716736483, 1099716803043, 17317858801, 4432962033, 56824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56828, 4349078017, 16833024, 16833028, 30102023689, 16833032], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609228, 3779088, 3845648, 33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69746325545, 35521084481, 26712897825, 30655681825, 17754076449, 13123570009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203350363, 1100153019739, 1100035574167, 1100035575191, 1100035576215, 1099985245591], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4550407597, 1099934842287, 1099934908847, 1099934909871, 13274486193, 8912479665], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918062003, 1099666470383, 1099666471407, 56820, 56824, 56828], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365854209, 70888961, 16833024, 25823836677, 16833028, 33609224], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609228, 12888675857, 33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65468204077, 26964706373, 26561971497, 26293608745, 13425556777, 8845446501], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136241511, 1100102688103, 1099968466343, 1099968467367, 1099918136743, 9013141929], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862150057, 4516854185, 1099934908847, 1099934909871, 1099934910895, 1099716803043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716804067, 21629535721, 8761482729, 4382633453, 1099666470383, 56820], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56824, 16833020, 16833024, 54111749, 54178309, 16833028], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609224, 33609228, 21478606353, 3779088, 33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69662576689, 9935901769, 26511642901, 26276834581, 9180924181, 1100018800015], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968469391, 1099918138767, 8962813329, 8828598673, 1100052350355, 1099968465319], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968466343, 1099968467367, 17435234761, 4600735177, 1099800623567, 1099800690127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800691151, 4382633453, 1099666470383, 56816, 56820, 56824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833020, 16833024, 54111749, 54178309, 16833028, 12922229257], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37331465, 33609224, 33609228, 33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65350835253, 1396300877, 26427825429, 26209794325, 4886025493, 8895707521], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119393667, 1100119460227, 1100119461251, 1100119462275, 1099851029919, 1099918136743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867806119, 13224222133, 4634291637, 1099901285815, 1099800623567, 1099800690127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800691151, 56816, 56820, 56824, 16833020, 16833024], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833028, 8627265033, 4332300809, 37401097, 33609224, 33609228], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group6
