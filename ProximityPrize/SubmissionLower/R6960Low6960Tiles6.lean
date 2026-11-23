import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
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
  ⟨unpack [18959698951, 32148693007, 86843277339, 52836471863, 35488481535, 31093056767], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39330809087, 17537346927, 4702781807, 17604380067, 13208754595, 8897079715], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34716650931, 1099801998791, 1099801999815, 1099802000839, 1099751670227, 1099751671251], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [122595823, 1099634224623, 1099634225647, 8695749107, 4384007667, 25858696695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17268834807, 38693122563, 34364460555, 8595084811, 5154315], by decide +kernel⟩
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
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27920373771, 40420520983, 82582199331, 27167403071, 31042723087, 30791204111], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34851364111, 13208755591, 8846749071, 8762866063, 1100036883855, 1099852331451], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852332475, 1099852333499, 38978270655, 17470094783, 8897008063, 1099768442319], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099768443343, 1099768444367, 4501446103, 4417562071, 1099600668151, 1099600669175], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25841917435, 17252055547, 8611794439, 4300118539, 5153291], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32199222287, 52886258715, 82498451499, 30774360323, 30606727427, 13494040835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35069183327, 22201198943, 8980896135, 8880301447, 8779641223, 1100003327383], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003328407, 1100003329431, 13275857327, 8897008047, 1099869106615, 1099869107639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099869108663, 1099768440271, 1099768441295, 1099768442319, 156147175, 1099667775975], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4367159803, 4333672955, 21928455, 34364671499], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36326813715, 82447914013, 35539231803, 31176873195, 30875022571, 39129552107], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100271762775, 1100271763799, 1100271764823, 17537275231, 13175269727, 1100238207327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936213415, 1099936214439, 1099936215463, 1099936216487, 17553978799, 8964114863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4585264567, 4484603319, 1099869103543, 1099667774951, 1099667775975, 38793720299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25858628087, 55416319, 55482879, 17184945675, 4300048907, 4300050955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44514294807, 78153082917, 18426475581, 26747758835, 26479461619, 26278207731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100187876715, 1100187877739, 1100187878763, 8897012079, 1100171095407, 1100171096431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100171097455, 1100171098479, 34884631951, 26244505999, 13242303903, 8829900191], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099852325307, 1099852326331, 1099852327355, 4400715227, 1099718106587, 13074529759], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4383935991, 88970743, 89037303, 21513396737, 12923533827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44480940059, 86625645609, 30891799771, 30640280793, 17755452633, 13242307943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8846681447, 1100204650855, 1100204651879, 1100204652903, 1100204653927, 1100204654951], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100204655975, 30606444939, 21983095179, 13225460131, 8863453603, 1099936212391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099936213415, 1099936214439, 1099835481535, 1099835548095, 4400714215, 1099667708391], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8678900215, 4383935991, 38639107, 21496621575], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [56996877341, 61023751217, 22050278667, 21865800969, 9014525193, 30874883383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18006897975, 17738533175, 8813127019, 1100187873643, 1100187874667, 1100187875691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100154322291, 1100154323315, 1100154324339, 4534934935, 1099952989603, 1099952990627], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099952991651, 8863451583, 4501378495, 1099751661011, 1099751662035, 105747955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099617442291, 30136817147, 12940244477, 8645346815, 38638083], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [56946614305, 48205961269, 17654716701, 17486949661, 1100506644767, 1100506645791], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26630316335, 17939856687, 17688269103, 1100187872619, 1100187873643, 1100187874667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100187875691, 1100187876715, 1100020098451, 1100020099475, 4652372395, 4518156715], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919434155, 1099684485603, 1099684552163, 13040975335, 4451044839, 25825141247], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38639107], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69596703781, 22620778557, 26697493755, 22167718139, 26177544441, 1100288539987], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100288541011, 1100288542035, 8897012063, 1100238204255, 1100238205279, 1100238206303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100238207327, 8997669283, 4618818979, 1099952922019, 1099919434155, 1099919435179], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919436203, 21664394715, 8796341723, 105747955, 1099617442291, 21860869], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17184878089, 8595014153], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61073946665, 18359366717, 22285089039, 22016790797, 17570834701, 1100254985563], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100254986587, 1100254987611, 1100171094383, 1100171095407, 1100171096431, 1100171097455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100171098479, 8930562451, 4568489363, 1100020098451, 13124794835, 8796342739], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099734883799, 1099734884823, 156079591, 1099667708391, 4316826117, 21860869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65268319277, 1297007685, 22234825979, 26211097849, 13326268665, 8930565479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100204648807, 1100204649831, 1100204650855, 1100204651879, 1100204652903, 1100204653927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100204654951, 1100103992703, 13175195059, 4568487347, 1099852258747, 1099852325307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099852326331, 88970743, 89037303, 8662124027, 4350382587, 5083657], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56728784945, 22050345225, 17604389129, 8997747977, 1100171099503, 1100171100527], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100171101551, 1100154317171, 1100154318195, 1100154319219, 1100154320243, 1100154321267], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8930562455, 4568489367, 1100003321239, 1099718106587, 1099718107611, 4434268651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [139368939], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
end Low6960Allocation.Group6
