import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass20

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23725673479, 44984312847, 129760317471, 1985465415, 48390951163, 48189833467], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26815738107, 30338875871, 21749015007, 47417796087, 13058488823, 173591031], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43022374415], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 135 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 135 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 135 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36528003083, 49212701719, 104108157991, 39650159903, 39381800223, 18024480031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21816120783, 13192637903, 8763522539, 4435003883, 43156454895, 34566662639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4367814157, 72927759, 1099584556559, 34415450641, 4334337559, 39372311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12907490843], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 135 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 135 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 135 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40873894927, 61627976735, 74194454579, 30775085391, 30557055311, 5005429071], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43542334855, 30707972487, 13192636871, 8864184775, 1099886544327, 17336605179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099668441595, 1099668442619, 4384668171, 89702923, 8629235219, 42988817943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8595746335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 135 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 135 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 135 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45001355283, 61561003043, 57098541111, 22101334375, 21883236711, 4837656935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39297768827, 22168372603, 8830562763, 4535664075, 1099869767115, 1099735550443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735551467, 47384310271, 13024861695, 4434931199, 4384667143, 1099618106887], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099618107911, 34398888471, 22591004], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 135 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 135 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 135 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45035174935, 65688266791, 40002562107, 35170642263, 22235483479, 17806370135], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13226195327, 4686662015, 4502108627, 1099836211667, 1099836212691, 1099785882079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099785883103, 8780228079, 4485329391, 1099618105863, 1099618106887, 43039079947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17252716047, 8662786575, 34382178843, 4300779039, 5813788], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44968200219, 65604449323, 27201614911, 30909232455, 22168376647, 13544959303], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8864185751, 1100087871895, 1100087872919, 1099802656219, 1099802657243, 1099802658267], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4502040039, 4434998759, 13091968495, 4502037999, 43089414655, 89699851], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099601328651, 25825801747, 56070673, 4317556251], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48994800671, 61275997231, 14383824963, 22403253571, 22118112579, 9249994051], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100003983787, 1100003984811, 1100003985835, 1100003986859, 39046108611, 4686511553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13091970527, 4518817247, 4418221539, 1099769101795, 1099634882051, 1099634883075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8646008339, 4351044115, 39367191], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [48944603171, 61192179763, 1599589447, 22285816115, 22017452339, 9182953779], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8897669559, 4552373687, 1099953651127, 34784764347, 21899937211, 1099903320515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099903321539, 1099903322563, 1099886546375, 8763448823, 1099685213687, 1099685214711], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4418152963, 123253251], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [53021535271, 48357613627, 17839923527, 17588270407, 4787325255, 30691126667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17806298507, 4602705323, 1100003982763, 1100003983787, 1100003984811, 1099920099775], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920100799, 8830558695, 4468485607, 1099685213687, 1099685214711, 56077843], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56144403], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [57098401835, 31345586239, 30825412955, 17873475931, 13410741595, 8948071795], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100238866803, 1100238867827, 1099869765067, 1099869766091, 1099869767115, 4518817243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4434998747, 1099651659263, 1099651660287, 13008083459, 4418152963, 25825802771], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56071697, 56144403], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [57014584367, 18578127939, 26564003147, 17839923531, 9182885195, 1100104647059], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100104648083, 1100104649107, 1100104650131, 4434998747, 1099802656219, 8813781483], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4468485611, 1099651659263, 1099651660287, 21564458507, 89628169, 4317556247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [22588956], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [52719685683, 10055304263, 18057957711, 17772815695, 9115777359, 1100020762023], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100020763047, 1100020764071, 1099852986831, 1099852987855, 1099852988879, 8830559711], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4451709407, 106476039, 1099618104839, 4317488667, 22588955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 20 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤138 ∧ 7+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group20
