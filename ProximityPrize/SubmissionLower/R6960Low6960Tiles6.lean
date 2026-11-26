import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass6
set_option Elab.async false



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
  ⟨unpack [2164329477, 1023479819, 5989798923, 19278339085, 48673075217, 87043498017], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [40185148477, 35469922561, 39547461941, 35118418229, 39195356469, 43624183145], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4617655725, 17502481849, 13140410809, 8828735929, 25891015149, 17301153261], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349219317, 8644116985, 4365995513, 1099565881855, 20698629, 8593783305], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4298884617], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 130 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14714476555, 31962703889, 82630756377, 69947856949, 39698254097, 35319607569], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39363056913, 26193083741, 1100236904799, 21797377469, 13207514557, 38960110017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828665285, 8744782277, 4449883589, 43154620889, 4365994477, 1099632988655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099632989679, 34430611961, 4332371457, 4315661825, 37473793, 3917321], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3918345], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27734582285, 61373890585, 86943038509, 10187558985, 30924045609, 34933873961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26327302441, 43724849477, 35135122757, 8828666289, 8744783281, 17502412213], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13157183925, 1099783985611, 1099716873691, 1099716874715, 1099716875739, 43104216549], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [121291245, 1099632920047, 1099632986607, 21545718265, 8660890105, 4332371449], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38691951105, 30102092289, 8610556421, 20626949], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 130 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36190826513, 82597401629, 57063023673, 39631213837, 35202235661, 34984206605], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17552819553, 1100220127587, 13291332005, 13173961125, 8828666277, 1099834248639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834315199, 1099834316223, 43221660105, 25974898137, 17368193497, 1099683250659], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683251683, 1099683318243, 4416254445, 4382702061, 38725508601, 20625925], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20626949, 17183709705, 8593780233], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 130 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48757357589, 86842240037, 27182874689, 35302829321, 35068088585, 39128249609], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17502483837, 43523587457, 34883463553, 8795113877, 1100002088343, 1100002089367], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535963573, 13190735285, 1099783915979, 1099783982539, 1099783983563, 4516918733], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4449811917, 1099767137743, 21579271661, 1099599363575, 1099599364599, 30102022657], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21512161793, 8627332609, 4332368385, 20625925], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57162942489, 82547408941, 10070118473, 30907269393, 34933940497, 22049113361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39396395353, 30789824857, 13291331997, 13157183901, 8795111837, 1099968466335], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901424047, 1099901425071, 1099901426095, 1099750359507, 1099750360531, 1099750361555], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368191453, 4466586081, 4382702049, 70957561, 1099582586363, 8627332609], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30068535817], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57196696605, 78252510257, 1547360329, 30806674709, 30588644629, 13475958037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39346132325, 26444594533, 13207514517, 8845442453, 8744782229, 1099934979495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834247615, 1099834248639, 1099834315199, 1099834317247, 13157112265, 8845437385], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733581271, 1099733582295, 1099733583319, 4382701029, 54179325, 1099565808127], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25773571593, 4298811913, 3846665], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 130 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61391134753, 65434786869, 26360716585, 26176239913, 4852471081, 35135054161], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26444596561, 8912550285, 8795112845, 1100035576207, 1099884647859, 1099884648883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140337081, 8811884985, 1099817469379, 1099817470403, 1099817471427, 1099700026847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700027871, 4365922801, 1099616139763, 21562492405, 12972629493, 4365921785], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20624901], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69796588581, 44111015997, 31007862057, 26511707433, 26276899113, 17468933461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100253682007, 1099968464287, 1099968465311, 1099968466335, 1099968467359, 1099968533919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979655077, 8845440421, 4500144549, 1099716805083, 17368190429, 13039739357], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [154842597, 1099666471399, 1099666472423, 8610554373, 4315590149, 1099515550219], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78235596841, 22787245125, 31041485065, 26528487689, 30538315017, 13207516541], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828667265, 1100085907843, 1100085908867, 1100085975427, 1099834246591, 1099834247615], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834248639, 13190666689, 8862214593, 4466587085, 1099767135695, 1099767136719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25857456629, 12972561909, 70956537, 1099582585339, 4315589125, 20623877], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69746459693, 18525833285, 30789829925, 26327229733, 21898117413, 1100052421003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811889037, 1100035575183, 1100035576207, 1100035577231, 8962811309, 8845439405], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4516920749, 1099800692167, 1099800693191, 21696710101, 13090004437, 1099666472423], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666473447, 4382700013, 1099632916975, 20623877, 20624901, 12888743433], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4298812937], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73923989553, 1497028681, 30806675725, 26327232781, 13459180813, 8962879893], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811888021, 1100002019735, 1099985243547, 1099985244571, 1099985311131, 1099884648883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17485631937, 8895768001, 1099767135695, 1099767136719, 1099767137743, 4382700017], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616139763, 3846665, 3847689], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65384455221, 26411048221, 26193017117, 4869248285, 13140408709, 1100069128583], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069129607, 1100069130631, 1099918202283, 1099918203307, 13224222137, 8862215609], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466588101, 1099800691143, 1099800692167, 1099616139763, 1099616140787, 4349144573], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54179325], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
