import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 1040257035, 4966192137, 23069858829, 69762102293, 87060346921], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14599900229, 31560242349, 35419459845, 39731541265, 39647927569, 39279035713], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39144959297, 17468796345, 13140345273, 26008323545, 17418461657, 4399419873], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716745699, 4399415801, 4349086201, 1099599303167, 1099599304191, 38725377537], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660825601, 38708449797, 37341705, 1099548970507], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 132 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10704590859, 27617010701, 61373759513, 86976461869, 10254602313, 30923980081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34950585649, 26327171377, 39513637189, 35168545093, 8845377977, 8761494969], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17502346689, 13123498433, 43255014857, 1099750300123, 1099699965415, 1099699966439], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699967463, 4349084153, 1099616078331, 8677601789, 4365860349, 21545651713], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708451845, 34396924425, 37340681, 12888614417, 3784209, 3785233], by decide +kernel⟩
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
private theorem i54 : checks (tilesOf batches) 132 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27617010701, 65551286297, 86926196781, 5926081609, 35101507877, 39144891685], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13526158629, 39631012137, 31041284393, 17535903133, 13157054877, 8845379997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43255014857, 1099783853523, 1099783854547, 21713357273, 13106717145, 1099733518815], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733519839, 1099733520863, 4466522593, 4399415777, 4416123381, 1099599299071], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599300095, 20560397, 20561421, 8593646097, 8593714705], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 132 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36157206545, 74091222045, 65568939061, 35369735457, 30907136289, 30722726177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26159397193, 4835628361, 8845310377, 8778270121, 1099951624619, 43288637889], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17452014017, 8845307329, 1099800630735, 1099800631759, 1099750295003, 1099750296027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750297051, 4399413737, 1099683185131, 25924434413, 17317795309, 4365790721], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332303873, 4349012485, 1099565743623, 20559373, 20560397, 12888610321], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8593647121], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 132 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44546145301, 82563917861, 35672012865, 31108393229, 35067955469, 30638845197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13106793853, 39178157461, 30588364181, 13190606233, 8845311385, 8778271129], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901294007, 1099901295031, 21797243321, 13173825977, 1099817404875, 1099817405899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817406923, 1099750292955, 1099750293979, 1099750295003, 4416123365, 4382636517], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599297023, 8660754945, 4349013505, 54113797, 17217062409, 12922165769], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4298747409], by decide +kernel⟩
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48740648985, 78302640169, 22837445701, 30907136281, 34917030169, 30504697113], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39262112129, 30605209985, 13123501445, 1100069064079, 1100069065103, 1100069066127], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052289935, 13324753313, 8979524001, 8845309345, 1099850957251, 1099850958275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850959299, 4416189921, 1099716738531, 17351348709, 4365789697, 70889985], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [70891009, 1099582519811, 25823769093, 17233907205, 4315457037, 8593646097], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61357315101, 78235668529, 26545131793, 30571736337, 13459049745, 35218740549], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545060165, 13207383437, 8845311373, 8778271117, 1100001957279, 1099968403871], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867736511, 1099867737535, 1099867738559, 13173822925, 8828528077, 1099800624591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800625615, 1099800626639, 4416123357, 1099733514719, 87667197, 87668221], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25840548353, 4332234249, 37269001, 55820, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69796388897, 56895120441, 35269140773, 30772987173, 26226435385, 21814100281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100354279739, 8794980749, 1100069064079, 1100069065103, 1100052288911, 8962745769], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828531113, 1099951553963, 1099850957251, 1099850958275, 1099850959299, 21713356241], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13089938897, 188264933, 1099699959271, 1099699960295, 34430411265, 8643976709], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349012485, 55812, 55816, 21495318029, 55820, 54800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74024381477, 39849538621, 31024508185, 26545130777, 30538180889, 13173901661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186507615, 13224159629, 8862087565, 8778270093, 1099968401831, 1099934848423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867735487, 1099867736511, 1099867737535, 1099783846355, 1099783847379, 1099783848403], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17418390997, 8845304277, 4449676769, 1099716736483, 30135512577, 55808], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 37269001, 37335561, 55816, 54796, 55820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17183575569, 54800, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78235531305, 22753559621, 30991022345, 26528422153, 30538249481, 1100102620539], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052289915, 13173831037, 8828601725, 1100136173951, 1099884512699, 1099884513723], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884514747, 13207378369, 4634225089, 4533563841, 1099834112455, 1099834179015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834180039, 25941211625, 13056382441, 87667197, 1099599295999, 55804], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55808, 55812, 54792, 55816, 54796, 55820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4298679825, 54800, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73957409837, 14264355909, 26679346449, 26410983697, 26209729809, 8878865789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795048317, 1099985180051, 1099951626643, 9013076397, 8862084525, 4516788653], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918068147, 1099918069171, 1099901292979, 1099834180039, 1099834181063, 1099699960295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699961319, 21629470189, 8744639981, 4382567921, 1099649627635, 55804], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55808, 54788, 55812, 37269001, 37335561, 54792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55816, 54796, 55820, 53776, 54800, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73907146801, 1463343177, 30772990217, 26310324489, 13425495305, 8945971597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811756941, 1100069063055, 1100069064079, 1100052287887, 1100001957263, 1099834186155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535832501, 8929191349, 1099834179015, 1099834180039, 1099834181063, 188264933], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699959271, 1099699960295, 55800, 55804, 55808, 54788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 4332234249, 37269001, 54792, 55816, 17200353805], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54796, 55820, 53776, 54800, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65384389685, 26410982685, 26192951581, 4869182749, 8895641989, 8795047301], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085842311, 1099884516779, 1099834186155, 13207379385, 4634226105, 4516787641], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884512699, 1099884513723, 1099884514747, 1099783847379, 1099783848403, 137999857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649628659, 55800, 55804, 55808, 54788, 55812], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8627199497, 4332235273, 54792, 55816, 20558349, 54796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55820, 53776, 54800, 55824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group4
