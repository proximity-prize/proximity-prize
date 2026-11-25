import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass41

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group41
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27907066887, 40642357267, 86931099679, 48528335931, 35307671831, 35072931095], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39133092119, 17389896047, 13279402379, 13161965963, 8850291083, 1099922982307], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099922983331, 1099922984355, 1099922985379, 21751821763, 13161958851, 1099755207115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099755208139, 1099755209163, 4421036495, 1099738427855, 1099738428879, 4404256235], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4353926635, 38747056623, 1099604209135, 34401833467, 42182139, 1099553810939], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 128 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 128 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 128 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36413970443, 53091318807, 82619494443, 18597789763, 30861848863, 30643818783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30476054815, 13111636355, 39166426507, 30526301579, 1099973312919, 1099973313943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099973314967, 1099973315991, 1099973317015, 13212291499, 8850219435, 8749559211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099822315963, 1099822316987, 1099721584083, 1099721650643, 1099721651667, 17322706399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4370702827, 1099620919787, 38713432567, 25811903995, 17222042107, 4337146363], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25403903, 25404927, 8598558211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 128 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 128 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 128 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40675779599, 65640746015, 74012855347, 26415959331, 26231417123, 13380142371], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35173518659, 26533327171, 8866998675, 8766338451, 1099990090131, 1099956536731], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099956537755, 1099956538779, 1099956539803, 13178736063, 8799886783, 1099805537727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099805538751, 1099805539775, 1099704805847, 1099704806871, 1099704873431, 43025245683], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4370701811, 75736563, 21517005307, 12927076859], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 128 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 128 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 128 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40743088147, 61396178979, 65439700023, 22120994091, 21919673643, 13329810731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35072858451, 22171254099, 8816668055, 4521769367, 1099973312919, 1099973313943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099973314967, 1099973315991, 1099973317015, 8850216391, 4538474951, 4454590919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099738427855, 1099738428879, 1099738429903, 1099738430927, 1099604142575, 1099604209135], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17222041083, 8632111611, 34385058303, 8626691, 8627715], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 128 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 128 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 128 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44870482967, 74029492263, 35576328255, 31029618971, 26483001627, 22053889307], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13145259363, 1100191419747, 1100191420771, 1099922980259, 1099922981283, 1099922982307], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099922983331, 8833443239, 4504924583, 1099906202023, 17423370695, 8799886791], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099688096219, 1099688097243, 38797393379, 30207534563, 142846435, 1099654475235], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4337147387, 42182139, 17188488707, 8598559235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44836997147, 78240642091, 18513903683, 26818540811, 26516623627, 26281749771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100057201027, 1100057202051, 1100057203075, 8900554119, 8816736647, 1100040422791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13178737087, 8816665023, 1099805538751, 1099805539775, 1099805540799, 1099721584083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099721650643, 1099721651667, 38814173663, 25929347551, 4353925623, 58960375], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48930706463, 73945744431, 5729668167, 26633995535, 26365632783, 21919677711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8833514875, 1100090755451, 8967659935, 8816668063, 4521769375, 1099939761567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099939762591, 38998791603, 26080411059, 1099839095223, 1099839096247, 193179095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [193245655, 1099704874455, 1099704875479, 1099704876503, 8749554143, 4337149435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21500231167, 12910302719], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57235496995, 61111179319, 26382407971, 21902898467, 4840541475, 34972262771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22087435635, 8833447307, 1100023644555, 1100023645579, 1100023646603, 1099906207143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099906208167, 13145185719, 4555255223, 4421105095, 1099771985351, 1099637765607], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099637766631, 8648891895, 4353927671, 59027959], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61396315175, 44099151931, 17641482575, 13229079887, 4672769359, 35056151895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22104215895, 4504993187, 1099922982307, 1099922983331, 1099889429931, 1099889430955], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8799889855, 4488213951, 1099704876503, 1099704877527, 17272377839, 4387481071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [92583407, 1099604212207, 4370771443, 30090096127, 17205267967], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61329209387, 31314916415, 30828296523, 22070663499, 17591152971, 8867071339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100157866347, 4605587887, 4521769391, 1099872649647, 1099872650671, 1099872651695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099872652719, 13061298651, 8716003803, 1099637766631, 1099637767655, 4337150459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4320440827, 30073387523, 8696323, 8697347], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61278946351, 18564235331, 26566886723, 17859584323, 17607931203, 1100006869391], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100006870415, 1100006871439, 8816735659, 1099889426859, 1099889427883, 4387550691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099654544867, 12994191847, 4421104103, 42252795, 25778423299, 8598561283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4303662595], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61195063347, 5796777031, 26533400883, 21986782515, 13346587955, 1099922982307], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099922983331, 8900554159, 4588878255, 4471439791, 1099872652719, 1099872653743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099688100315, 21584122347, 8699226603, 59030007, 1099570658807, 4320441851], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8697347], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((41 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 41 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group41
