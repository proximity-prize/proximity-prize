import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass11

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2164329477, 1006702601, 10352071691, 27700961293, 86875257877, 87111012401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35486961917, 44060392705, 39715301633, 34984333653, 34816636245, 9214679381], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17435506117, 8845576645, 8778470853, 47432938973, 25891148269, 17301286381], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633123823, 87873013, 1099599501815, 1099599502839, 38692088321, 8610693637], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315729413], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 130 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [18942531593, 44461992977, 86959609889, 57146977341, 39631411489, 35219144993], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39262528801, 21797588345, 43540426109, 43322382769, 17536099765, 13190871477], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13090212277, 4433172937, 1099784053195, 4399614441, 1099649831403, 1099649832427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633056239, 1099633057263, 30169334257, 17284440561, 8627468801, 4332504577], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20762117], by decide +kernel⟩
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
private theorem i54 : checks (tilesOf batches) 130 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27852153869, 61424353305, 86943104045, 18710515785, 35168812329, 34950783273], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30572004649, 43724980561, 35135253841, 13123765669, 17502544313, 13157316025], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466726329, 1099851161019, 1099851162043, 4416390625, 1099683384803, 1099683385827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666609639, 1099666610663, 21596180973, 8644244989, 4332503549, 47281939969], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37538305, 12888877577, 3981833, 3982857], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 130 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36274843665, 82614244381, 65569137721, 39681676561, 35235921169, 35017892113], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26126042445, 1100304146767, 8845575589, 8761692581, 1099935047079, 17502544305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895837617, 8828797361, 1099750494675, 1099750495699, 1099750496723, 47432872413], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30219664869, 17317993957, 1099666607591, 4366057965, 1099633052143, 4349277693], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332502525, 8627466753, 1099549165059, 38658531849, 12888808969, 8593911305], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3980809, 3981833], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 130 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48790977557, 82631289893, 39950400577, 35286183197, 35034665245, 30605554973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13123769721, 43490164105, 34900371849, 13157250465, 8828798369, 8744915361], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867938231, 1099867939255, 21763953089, 13123692993, 1099784049099, 1099784050123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784051147, 1099700159967, 1099700160991, 1099700162015, 4433164773, 154976741], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21529071101, 8644241917, 4349277693, 12888876553, 3980809], by decide +kernel⟩
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
private theorem i55 : checks (tilesOf batches) 130 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53035878425, 82564250669, 22871264325, 35185589525, 34934006037, 30521672981], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43523787137, 30622184833, 13140542853, 1100002153879, 1100002154903, 1100002155927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002156951, 13325017505, 13157249441, 8828797345, 1099800825287, 1099800826311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368323549, 1099700158943, 1099700159967, 1099700160991, 8711352805, 154975717], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315722245, 20756997, 30068667913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57213539357, 86792244273, 1497096269, 35084930313, 39128379657, 9265010953], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39329486185, 26444660073, 13291467133, 13190873469, 8828801405, 1099901492655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867939255, 17502542265, 8879058361, 1099851157947, 1099851158971, 1099851159995], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433166793, 1099784047051, 1099784048075, 4416387553, 1099633050095, 1099633051119], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332498433, 4332500481, 37535233, 12888807945, 8593910281], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 130 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846917153, 65434919993, 26327295277, 26159595821, 4835826989, 39497261361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545326385, 13106987405, 1100035707279, 1100035708303, 1100035709327, 1099884715443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884716467, 13174023605, 8845571509, 4433166789, 1099800824263, 1099800825287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649827307, 1099649828331, 21596178925, 12989473261, 4366054901, 1099599494647], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708863485, 4349276669, 12888875529, 3979785], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 130 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74074909733, 48372560957, 35252628773, 26545393957, 30538444069, 17485843789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100304146767, 13207580057, 8862350745, 4533832089, 1099985375643, 1099985376667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985377691, 1099985378715, 1099733715415, 1099733716439, 1099700157919, 1099700158943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700159967, 17351545313, 8761615841, 4433162729, 4366055913, 34413899261], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54311421], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041423913, 35554771009, 31008061729, 30689368353, 22015621409, 13140545889], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220260707, 1099951821219, 1099951822243, 1099951823267, 1099951824291, 8845572517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4517053861, 1099935042983, 17502542265, 8879058361, 1099700159967, 1099700160991], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382833125, 1099666604519, 54311421, 1099565940223, 4332498433, 4315723265], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30085446149, 12888807945, 8593910281, 3978761], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763302445, 27015170117, 30840292649, 26344072489, 21914960169, 1100153149811], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153150835, 1100153151859, 8828797333, 1100002151831, 1100002152855, 1100002153879], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190800821, 8828794293, 1099750490579, 1099750491603, 1099750492627, 25924699621], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13039804901, 4382832113, 1099616271859, 4332499457, 3979785], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [86708359217, 30924181749, 34900455669, 13509580021, 13291467129, 13157319033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795246969, 1100035710351, 1100035711375, 1099901489583, 1099901490607, 1099901491631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466721213, 1099834378687, 1099834379711, 21747175877, 8879057349, 4483495389], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382834141, 1099649828331, 1099599494647, 1099599495671, 17183773193, 8593909257], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73924189237, 26528619793, 26293811473, 13425759505, 8912615825, 8812021137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018930067, 1100002153879, 1100002154903, 1100002155927, 1100002156951, 17401880009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812016073, 1099784046027, 1099784047051, 1099784048075, 171752929, 1099683381731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12922363393, 8627465729, 37534209], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 130 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 11 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group11
