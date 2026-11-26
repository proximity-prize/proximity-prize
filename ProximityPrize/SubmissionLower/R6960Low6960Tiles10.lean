import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass10
set_option Elab.async false



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
  ⟨unpack [2231438341, 15016464395, 32214753293, 74276225049, 78605355057, 43825971529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39447326025, 30672983401, 26277426537, 1100254204267, 13090600421, 8762082789], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21596575229, 13006646781, 38725751305, 34431069705, 25841209865, 47282272785], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4332897809, 37932561, 8594308633], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i51 : checks (tilesOf batches) 134 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23691270153, 40637509649, 87027243041, 40202447933, 39631804721, 35169206577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43474068785, 17570047409, 13191199153, 8879524273, 43138232813, 25925026293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17335164405, 138594809, 1099650223611, 1099650224635, 8694970877, 4366452221], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8627859985, 37930513, 4299341337], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36358923277, 74226026521, 69981933617, 43809261885, 35185980733, 26361239905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26193540449, 1100287758691, 8862676425, 8795636169, 4467117513, 43138164205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17351940593, 8762011121, 1099667000823, 121815549, 1099633444351, 1099633445375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30152881669, 17268053509, 38709187085, 4349671949], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40620732433, 74226227233, 52852400185, 39497587013, 30823907653, 21982454133], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21814688117, 1100203872631, 8812411337, 4500669897, 1099851550155, 43155010025], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13056975345, 4467044849, 25891471869, 13006642685, 1099633444351, 1099633445375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4366449153, 1099616666115, 34397445649, 21150229, 21151253], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48976116757, 86926715941, 18778013761, 35320130845, 30857531677, 30656278813], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13157642669, 43373116853, 34766547381, 4534223297, 1099885103555, 1099885104579], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885105603, 17435824605, 8845895133, 4467044849, 4416780785, 1099633443327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633444351, 21563018757, 37927441, 37928465, 34363959833], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53153843225, 82615041069, 5960223813, 35169205537, 30689763617, 17804935457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39178815901, 30589022621, 13258301881, 8879452601, 8795635129, 1099918657979], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099801218519, 1099801219543, 17402270181, 1099700551151, 1099700552175, 1099700553199], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4400001537, 105036289, 8611014165], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61525808157, 69814161457, 26512232761, 26277424441, 9198291257, 39380145517], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478607725, 8929783221, 8829188533, 8728528309, 1099834773967, 1099784439259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099784440283, 1099784441307, 13073750509, 8745232877, 4383226353, 1099683774963], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71480841, 71481865, 1099583110667, 4316047893, 4316115477, 25774030361], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65720246305, 52734959673, 35169132889, 22284305753, 22049496409, 17637160281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9064073561, 4550931913, 4483890633, 1099851548107, 1099834771919, 1099834772943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834773967, 13107305957, 4517375461, 1099650219515, 1099650220539, 71480841], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71481865], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69897841701, 35706155069, 35185913153, 22284374337, 22049564993, 13174489473], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153540995, 1099851547083, 1099851548107, 1099851549131, 1099851550155, 8879450573], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4534154701, 4467113421, 1099650219515, 17268052485, 8678123013, 30136102409], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17251274249, 71480841, 71481865, 4316115477], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74092214313, 18694127681, 30991677741, 30672984365, 26210318637, 8896231833], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4517447085, 1099968990639, 1099968991663, 17502935489, 8879451585, 4416780773], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099734106599, 1099734107623, 1099734108647, 88259077, 1099599887879, 4366380553], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71480841, 25824360973, 17234499085, 4332825105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69814092845, 10154526789, 26646381877, 26361241909, 21915352373, 8862743969], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099901880767, 1099901881791, 1099901882815, 13207970245, 8812343749, 1099734105575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099734106599, 1099734107623, 4416778749, 121813501, 21546173961, 12956311049], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4316114453], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69763829809, 26579341613, 26310978861, 9215068461, 8946560433, 8812345777], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099952211379, 1099868326343, 1099868327367, 1099868328391, 4400003561, 1099717329387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17351938545, 8762009073, 88259077, 1099599887879, 4366447113], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56979594293, 22133382473, 21915350345, 4852993353, 8845899189, 4534223285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099935435191, 1099817995731, 1099817996755, 13090528745, 8728456681, 1099683774963], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099683775987, 155367925, 1099666996727, 4349603341, 54703629], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤136 ∧ 5+a.j≤57 ∧ 1+a.t≤14 at box
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
