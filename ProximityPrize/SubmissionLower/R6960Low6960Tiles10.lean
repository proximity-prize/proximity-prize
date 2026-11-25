import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2181106693, 1006702601, 10133902347, 27633786893, 86858415125, 87094169649], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35503608061, 44077104381, 39698458877, 34967490897, 34816570705, 9214613841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207582145, 13090145729, 8761628097, 47516693965, 25941414373, 17334775269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666612715, 1099649766895, 1099649767919, 1099649834479, 4399547893, 4365995509], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38742354425, 20696585, 20697609, 38658467341, 12888813069], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14983043083, 32013101073, 82647599129, 78470682677, 39698319637, 35319673109], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39363122453, 30488051021, 4902870349, 13140475317, 13039816117, 21797443009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13173960129, 4399549917, 1099716875743, 1099716876767, 1099700100579, 1099700167139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43121060325, 4399545845, 4349216245, 1099599433211, 1099599434235, 34430611965], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [43003615745, 37471749, 37472773, 12905590281], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27784979469, 53002125337, 86943036457, 27233273925, 35185456421, 30773188901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43356174629, 43573985657, 34933861753, 17485707657, 8811957669, 8728074661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800762827, 1099800763851, 1099800764875, 17435367889, 13090139601, 8728067541], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750427095, 1099716873695, 1099716874719, 1099716875743, 21612892653, 43070727665], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349214201, 1099599431163, 34397056517, 8627400197, 4332435973, 20693513], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40334864401, 82597468193, 61290883129, 35420199185, 35202301201, 34984272145], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26075645265, 1100304081235, 8862287261, 8761627037, 1099985313183, 43389432229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13308174761, 13157183913, 8828731817, 1099800760779, 1099800761803, 1099800762827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25974898141, 17368259037, 1099700096483, 1099683316199, 1099683317223, 1099683318247], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8694510061, 4365991405, 54246913, 4315656713, 20691465, 12888742413], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48757357589, 86859082789, 35655368769, 35319672077, 39262392589, 39111538957], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136309115, 13241071997, 13157255549, 8811960701, 43540430209, 34900306305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21864550817, 13224290721, 1099884648887, 1099884649911, 1099834313155, 1099834314179], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834315203, 1099834316227, 4466653653, 1099750425047, 1099750426071, 21562559989], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8694508021, 4382766581, 8644175361, 1099565874691, 34397055493, 17183706637], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12888809997, 3913229, 3914253], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53002258457, 82547407917, 22837644357, 35168746769, 34917163281, 26276971793], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39279020409, 30672449913, 8862287245, 8761627021, 1100052422031, 1100052423055], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13324951961, 8962879897, 8879062425, 1099867869627, 1099867870651, 1099867871675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767204307, 1099767205331, 17418588629, 1099700092387, 1099700093411, 1099700094435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4399542773, 104577525, 8627398149, 30068601357], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61391000605, 86775402545, 35034534149, 30622266629, 13509580037, 39430018381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545257805, 13157184909, 8828732813, 1100052418959, 1099985311135, 1099985312159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985313183, 1099968536991, 17536031145, 8912547241, 1099800757707, 1099800758731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800759755, 4449876433, 1099767202259, 4382764537, 87799289, 87800313], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599429115, 12939074049, 8627399169, 38675240457, 25790414345, 4298877453], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099515617807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65602215969, 69679489081, 30605418785, 30420943137, 1100471853347, 35235782973], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511705405, 13157253497, 13039817081, 1099968532899, 1099968533923, 1099968534947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968535971, 13257843109, 8878993829, 8795176357, 1099851090367, 1099851091391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733646811, 1099733647835, 1099733648859, 4416319981, 1099649759727, 21596112369], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12989406705, 4349210113, 1099532395019, 8593776141, 4298877453, 3913229], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 131 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69813431333, 52617130045, 31007927597, 26528550189, 26293741869, 17536042305], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962955585, 8761623961, 1100002087323, 1100002088347, 1099985312159, 1099985313183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934982559, 8929323437, 8828728749, 4500210093, 1099817535943, 1099817536967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700093411, 1099700094435, 17351478757, 8761549285, 4382766569, 1099666537963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349210113, 54244865, 1099565873667, 1099549172231], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69779945513, 39799340097, 30940887337, 26427889961, 26209858857, 13157257557], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100236972375, 8895772053, 8811954581, 1100018863511, 1100002087323, 1100002088347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002089371, 1099985313179, 13173955017, 8828660169, 1099783979471, 1099783980495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783981519, 4416320993, 1099700092387, 25840744957, 12955850237, 54244865], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565873667, 4332431877, 4315656709, 1099532395015, 3912205, 1099515616783], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218953773, 18475569225, 30940890377, 30655751433, 30454498569, 13157254505], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102751619, 1100102752643, 1100085976451, 1100035645827, 13274621337, 8878994841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4584096153, 1099918199215, 1099918200239, 1099918201263, 21679998429, 13090069981], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416320993, 1099700092387, 1099700093411, 1099700094435, 4382764537, 54244865], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565873667, 1099549172227, 1099515616783, 57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940832305, 9935968329, 30773121297, 30555156753, 17653551377, 1100085973383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085974407, 13190738313, 8862286217, 1100069195147, 1100052421007, 1100018867599], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985314191, 17519251901, 8929322429, 1099783979471, 1099783980495, 1099783981519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4533760469, 4416322005, 104577525, 1099616206327, 1099532395011, 1099532393995], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57864, 57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73890569269, 30739635465, 26276969737, 9164282121, 8912616837, 8795179397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085974407, 1100018866583, 1099985313175, 1099951759767, 13291396525, 8912547245], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795175341, 1099867867579, 1099867868603, 1099867869627, 1099750426071, 188463585], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700092387, 1099700093411, 4365987325, 71022077, 1099532395011, 1099532393995], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57864, 57868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group10
