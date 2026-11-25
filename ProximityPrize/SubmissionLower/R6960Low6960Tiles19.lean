import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass19

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group19
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 6140727307, 19379001355, 40485989393, 87060337693, 57281325113], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43842557237, 39413514549, 21931796885, 21814428053, 4752071061, 39010636229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47567157705, 8778531305, 4483632617, 4433303017, 30253285869, 21663425005], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8677865989, 1099599633927, 38708931085, 54449677, 1099566078479, 47248456217], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299081241, 4115993, 4117017], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19362224137, 36358794257, 78503956509, 69998386229, 43792224573, 30957796669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588837225, 30437916009, 1100253879659, 8895970757, 13039946181, 4500412869], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21646646761, 8795305449, 4399679981, 4382970349, 43121192433, 1099649964539], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099599630855, 1099599631879, 38725704201, 71223817, 71224841, 4315791889], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42970192405, 30085513749, 17200685589, 4047385, 4113945], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32113828877, 78386316313, 82732290097, 39715226909, 35353357597, 30756540737], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34816700737, 9214743873, 13241266609, 13123830193, 8778535345, 1099784183259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099750625763, 1099750626787, 1099750627811, 21680132585, 13073492457, 4416455149], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700226543, 1099700293103, 43087635961, 4366121481, 34414030349, 54379021], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54445581, 8593975833, 4299011609], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36426035217, 74175435805, 69880945717, 39597921589, 30907465013, 26394533197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30471469389, 4869445965, 13140605361, 8795310513, 8728270257, 1099800958423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099784182235, 1099784183259, 13106978277, 8812080613, 1099733780967, 1099733847527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733848551, 4433230321, 1099683447283, 1099683448307, 47349117441, 25874431489], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17284569601, 20822549, 20823573, 34363630105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44747865109, 82648131621, 40000862273, 35336579361, 35068284193, 34867032353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845645189, 13258043805, 13123830173, 8778535325, 43305745861, 1099868069319], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21780794829, 13174154701, 1099834511823, 1099834512847, 1099834513871, 4433232345], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784112603, 1099784113627, 4416452089, 1099649891835, 1099633115647, 1099633116671], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34413963789, 8610752021, 4315787797, 17183837721, 12888941081, 4045337], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57280645145, 82614779949, 14365282377, 30924243233, 34934137121, 26277168417], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39346260341, 30756467061, 8845641117, 13308305837, 13174157741, 8812085677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968663983, 1099968730543, 1099968731567, 1099968732591, 1099767401951, 1099733778919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733779943, 1099733780967, 17351610865, 4450005493, 155040245, 1099666669047], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8610752021], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [69897245725, 74024917045, 30689433897, 26260322601, 9181189417, 39581144377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26696383801, 8912746913, 8795309473, 1100018995619, 1099918398907, 1099918399931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918400955, 17485830593, 8912743873, 1099800888791, 1099800889815, 1099800890839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [171817457, 1099683446259, 1099683447283, 12939270669, 8644307469, 37598737], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38658594329, 25773768217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69897379873, 61223969849, 35286245693, 26612565309, 22149898557, 26176502081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9046971713, 8879192485, 8761755045, 1100002218407, 1099951953331, 1099951954355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951955379, 1099817666003, 1099817667027, 1099817668051, 13107044833, 4533891553], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [188594669, 1099700223471, 1099700224495, 21545911817, 12956048905, 4299009561], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69880736805, 48406179901, 35219205437, 26478350653, 22032461117, 17536238933], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4701673813, 4517119405, 1099968662959, 1099968663983, 1099968730543, 1099918399931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918400955, 8879189445, 4550670789, 1099867996615, 1099733779943, 1099733780967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17385165289, 8795301353, 87931397, 1099599560199, 34414030349, 4332565005], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4043289, 4044313], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78319745065, 27099186245, 31041681693, 26528684317, 26310653213, 1100136436103], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136437127, 1100136438151, 1100136504711, 8946300321, 8812085665, 1100018994595], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13174086101, 8862411221, 1099784110555, 1099784111579, 1099784112603, 4366120441], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649891835, 30135843337, 54375949, 54376973, 4299008537, 4299010585], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74041623597, 18559585349, 30907532581, 26411312421, 26210058533, 8879194513], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100086103443, 1100086104467, 1100086105491, 1100086172051, 1100086173075, 13190931905], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812082625, 1099784110555, 1099784111579, 1099784112603, 25924765169, 13056713201], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382897657, 1099649891835, 4349342221, 37599761, 21478802969, 12888940057], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78235996209, 1530780749, 30873981201, 30605619473, 13476155665, 13241266581], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8862417301, 1100069326231, 1100018995619, 1100018996643, 1100019063203, 1099901623743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17469051349, 13123823061, 1099784110555, 1099784111579, 1099784112603, 4433229293], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700223471, 8627529233, 4332565009, 37599761], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65451760693, 1530780749, 30672723245, 21982199085, 9097303341, 8828861865], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099985439147, 1099985440171, 1099985441195, 1099985507755, 1099985508779, 1099901623743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13257973185, 8929521089, 4567448001, 1099733778919, 1099733779943, 87931397], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099599560199, 4315786773, 20821525], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 19 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group19
