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
  ⟨unpack [2214661125, 5620568073, 19379066889, 40469277713, 142525879325, 39933400285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [56643714269, 39547942109, 35218723145, 30555274657, 21931859361, 17452348853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13123897781, 1099918399927, 43288966597, 4416522737, 1099666739699, 1099666740723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8711484921, 4416520697, 25790538257, 17200684561, 20886033, 20892177], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20893201], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 133 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19379066889, 36342082577, 91204309021, 52936091705, 39748915473, 39497398545], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22418333969, 17553013129, 13224562057, 30303615453, 17418787293, 1099750624735], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099750625759, 1099750626783, 1099750627807, 8745040357, 4433298917, 34531257837], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8728260085, 54445577, 1099566074379, 4332632589, 37667341], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i54 : checks (tilesOf batches) 133 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32029942797, 53086340121, 99744249897, 1698551881, 35252762897, 39296212241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17922114833, 43490297229, 30639092109, 17569783213, 13190934957, 8862482861], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851288007, 1099851289031, 1099851290055, 1099733850595, 43154744805, 17368453609], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [155107825, 1099666736627, 1099666737651, 8694706681, 121552377, 8627529229], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30085435921, 4299076117, 4110868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 133 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36392546321, 65703007261, 74125644853, 30655944001, 26243609921, 9164476737], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39430214993, 26579008849, 8862414261, 8795374005, 1099918396855, 1099817734607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817735631, 1099817736655, 17435564497, 4584222161, 1099700290027, 1099700291051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700292075, 43070927353, 4399740409, 121552377, 34397183501, 12905716241], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20883985, 21478867477, 20887060], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 133 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40553561109, 74125304869, 48506907709, 35235915057, 26562234673, 17922041137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17536235885, 13207784813, 1099884842431, 1099884843455, 1099884844479, 1099884845503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761817541, 1099851285959, 1099851286983, 43188370909, 8795301349, 4500402661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21629864433, 155034097, 155105777, 1099666734579, 1099666735603, 30135839237], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53069629465, 82581224493, 14382124101, 30957862169, 30706277657, 13610368281], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245662601, 26360902025, 1099951951279, 1099951952303, 1099951953327, 1099951954351], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13274815925, 8895966645, 4601067957, 1099834507723, 1099834508747, 1099834509771], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17334898161, 4382961153, 87995905, 1099599624707, 1099599625731, 8593973781], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53052986397, 74041690161, 10070380617, 26579011881, 26344203561, 13492928809], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245731209, 22065937801, 1099951952303, 1099951953327, 1099951954351, 8979850677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828858805, 4533960117, 1099884840383, 1099884841407, 1099884842431, 13056710125], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416516593, 1099666733555, 1099666734579, 1099666735603, 20886033, 20887057], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299007509, 4107796], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61424951329, 65468603445, 22166674737, 26210055473, 9114145073, 35152093529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233711961, 8879191453, 8795373981, 1100019060127, 1099935175091, 1099935176115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935177139, 1099800953299, 1099800954323, 1099800955347, 13107043801, 4533890521], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416517605, 1099717066215, 71218693, 1099582847495, 21495645713, 8610749969], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315851281, 4108820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65602546725, 48406244413, 30957792577, 22284111169, 22049301825, 17536236885], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8946372949, 8761818541, 1099951950255, 1099951951279, 1099951952303, 1099951953327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951954351, 8862410189, 4533891533, 4466850253, 1099767398875, 1099767399899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633179131, 1099633180155, 17251012101, 8661082629, 54440457, 54441481], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20885009], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69796919337, 31327042625, 30941083949, 26411309357, 13560034605, 13140673905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203611507, 1100203612531, 1099935172019, 1099935173043, 1099935174067, 1099935175091], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207706057, 8845633993, 4500403665, 1099800952275, 1099800953299, 25857653249], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [87922177, 71218693, 1099582847495, 4349340169, 54440457], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65518797869, 22821061701, 30773314869, 26277094709, 9181184309, 1100102946187], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102947211, 1100102948235, 1100102949259, 13190931889, 8795305393, 1099851284935], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851285959, 1099851286983, 21696906721, 13090266593, 4416517605, 1099717066215], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399738365, 71218693, 1099582847495, 8593972757, 4106772], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69713170481, 5758637129, 26562302241, 30538575137, 4970171681, 13207711125], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8862481813, 1100052613527, 1099968730539, 1099968731563, 1099851288007, 1099851289031], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099767397851, 1099767398875, 1099767399899, 17402008033, 8812078561, 4483625445], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717065191, 20886036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65418271797, 26428087589, 21982198053, 9130922277, 8828860833, 1100002280867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002281891, 1100002282915, 1099968729515, 1099968730539, 1099968731563, 13224484293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828857797, 4416518621, 1099750621663, 1099616401919, 1099616402943, 4382961153], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [87995905], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 11 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤138 ∧ 4+a.j≤58 ∧ 1+a.t≤14 at box
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
