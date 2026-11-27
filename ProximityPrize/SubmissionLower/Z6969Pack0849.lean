import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0848

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles31
section Z6969Source2381
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group31
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23742647303, 40890803215, 82868063263, 53088918583, 43844455759, 35187554639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21967248811, 17554847147, 4770679211, 8713319943, 4418355719, 30120901143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21531040279, 22727199, 22728223, 12890845731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36544976907, 61678304279, 87062640683, 1884933191, 35170777411, 34969591107], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13595427139, 43592793483, 35003001227, 17487732183, 8881025495, 8813985239], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735681519, 21598146055, 1099618242059, 4368023055, 1099601462799, 43005581847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8612655647, 12890777123, 5946915, 5947939], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40840471567, 61611330591, 74177808435, 30775216459, 30557186379, 5005560139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43576085891, 30708103555, 13192767939, 8864315843, 8763655619, 1099735680495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17336736247, 1099702127095, 1099702128119, 4368022023, 1099635016199, 4384730639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4384798223, 42988807707, 38693982747, 39501339, 25792379423, 17202517535], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8612588063], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45018329107, 65755438115, 52837260343, 35170704739, 26530578787, 22017580399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17588401519, 4787456367, 4535727571, 4485463507, 1099853120979, 1099769235943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099769236967, 13075324403, 4502171123, 43089474051, 1099651792387, 1099651793411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [89830927, 89831951, 21514191387, 12924328475, 4300843555], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45018528791, 65688397863, 40002693179, 35153996119, 26413141335, 17588398463], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13192772991, 1100205444479, 4485463499, 1099886675403, 1099886676427, 8780360163], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4468684259, 17387064819, 8797135347, 1099685346811, 1099685347835, 43072765447], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [89830927, 1099601459727, 4334398995, 30120897047, 17236068887, 22654495], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22721055], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49095526427, 69832439851, 18695699523, 26748614967, 26429920567, 21984031031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100004116911, 1100004117935, 8847471027, 4552572339, 1099987338675, 43257317847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26094368215, 13209540055, 8847467991, 207204851, 1099718899187, 1099718900211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718901235, 1099718902259, 4351174167, 56208919, 42955393571, 12890772003], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53155681311, 73959704627, 26698352919, 26413212951, 13511541015, 39197234595], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26278919587, 1100004114863, 1100004115887, 1100004116911, 1100004117935, 8998462899], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8830693811, 1099987336627, 1099735609839, 1099735676399, 1099735677423, 13058546167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4334397975, 21497413151, 12907550239, 4300842531, 5877283], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53122261027, 61175534647, 26429920563, 17756172595, 9166308659, 34919113119], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22017508767, 4586058175, 4519016895, 1099937006015, 1099937007039, 1099937008063], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099937009087, 13142433235, 4552502739, 1099702122999, 1099702124023, 1099635013127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8662916627, 4351175187, 73052691, 21480703523, 5876259, 5877283], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61427051559, 39885252667, 30892584287, 22185282911, 17705837919, 13243103587], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100322883939, 1100322884963, 4519016891, 1099953783227, 1099953784251, 8813913567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4451840479, 1099718900211, 1099718901235, 123384327, 1099635013127, 17286401547], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8696472075, 56208919], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61326391339, 27134637119, 26681506123, 22151730507, 17689062731, 8830763399], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100171890055, 1099920228803, 1099920229827, 1099920230851, 4619611591, 4502173127], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099903450567, 13108876783, 8746804719, 1099685344763, 1099685345787, 4351174167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56208919, 56275479], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [57031492655, 18611813443, 26564134223, 17840054607, 13377320271, 1100088001947], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088002971, 1100088003995, 4502173127, 1099903450567, 1099903451591, 8813912559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4468616687, 1099685344763, 1099685345787, 21564589583, 8679693839, 39431707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39498267], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56964452403, 5844355143, 22269169987, 17789724995, 17538071875, 4619681179], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088001947, 1099953785275, 1099953786299, 8813914583, 4451841495, 1099752455659], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099752456683, 1099668567551, 1099668568575, 17319956995, 8696473091, 89829903], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4317619743, 22654495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52635933751, 22168575295, 17655510335, 4837787967, 4602836403, 1099987336627], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987337651, 1099987338675, 1099920230851, 1099920231875, 13125656039, 4518948327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [156939775, 1099668568575, 22654495, 22721055, 8595807779, 4300843555], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((31 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 31 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group31
end Z6969Source2381

-- Source: ProximityPrize.SubmissionLower.Low6969Mass32
section Z6969Source2382
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group32

private def m0 : MassCell 32 :=
  ⟨⟨1,3,59⟩,mass_cell 32 1 3 59 223 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2017299018819, 1510238412905, 1065310017285, 721805899265, 464610378845, 279506336025, 153175210805, 73197003185, 28050273165, 7112140745, 658285925, 356150, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 32 :=
  ⟨⟨1,6,76⟩,mass_cell 32 1 6 76 201 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1190503589161, 738458173802, 418762207150, 209982986698, 86811851198, 25413148810, 3424237102, 29549617, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 32 :=
  ⟨⟨1,9,84⟩,mass_cell 32 1 9 84 186 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1256920118276, 802325519812, 405980311972, 169699520900, 50446933348, 6998275396, 68263510, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 32 :=
  ⟨⟨3,10,86⟩,mass_cell 32 3 10 86 182 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 831015109623, 402819806391, 157412688559, 41226306783, 4123035975, 4663355, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 32 :=
  ⟨⟨1,12,88⟩,mass_cell 32 1 12 88 173 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 859828593810, 393272748526, 135011385794, 26327903974, 1026709210, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 32 :=
  ⟨⟨1,15,91⟩,mass_cell 32 1 15 91 165 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 905731898310, 394305907375, 111420510451, 13266826583, 51348283, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 32 :=
  ⟨⟨1,18,93⟩,mass_cell 32 1 18 93 158 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 932802756368, 395578149979, 91156124459, 5962771939, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 32 :=
  ⟨⟨5,19,94⟩,mass_cell 32 5 19 94 156 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 945341798017, 404638075803, 87410475391, 4826543822, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 32 :=
  ⟨⟨1,22,95⟩,mass_cell 32 1 22 95 150 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 955494747094, 403724163594, 70726296406, 1768530319, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 32 :=
  ⟨⟨4,24,96⟩,mass_cell 32 4 24 96 148 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 963804082594, 414354676892, 63462139944, 931275965, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 32 :=
  ⟨⟨1,28,97⟩,mass_cell 32 1 28 97 143 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 420199332758, 48338314578, 128506281, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 32 :=
  ⟨⟨1,33,98⟩,mass_cell 32 1 33 98 138 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 429506409168, 34107554768, 240274, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 32 :=
  ⟨⟨1,38,99⟩,mass_cell 32 1 38 99 134 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 447584666359, 26057842530, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 32 :=
  ⟨⟨1,47,100⟩,mass_cell 32 1 47 100 129 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 455698233812, 14582023526, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 32 :=
  ⟨⟨27,36,99⟩,mass_cell 32 27 36 99 136 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 445746621728, 28277484078, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 32 :=
  ⟨⟨45,43,100⟩,mass_cell 32 45 43 100 132 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 456082019616, 17858911377, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 32 :=
  ⟨⟨63,33,99⟩,mass_cell 32 63 33 99 139 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 442704427498, 30762500420, 4338880, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 32 :=
  ⟨⟨28,30,98⟩,mass_cell 32 28 30 98 141 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 432702239501, 40856106909, 47276001, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 32 :=
  ⟨⟨51,20,96⟩,mass_cell 32 51 20 96 156 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 963429247474, 405840243390, 68919099522, 2873553023, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 32 :=
  ⟨⟨72,26,98⟩,mass_cell 32 72 26 98 147 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 428220660508, 44388751408, 346384376, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 32 :=
  ⟨⟨69,41,100⟩,mass_cell 32 69 41 100 133 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 454735298570, 18958866036, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 32 :=
  ⟨⟨65,22,97⟩,mass_cell 32 65 22 97 152 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 414966331800, 57652307140, 1410014732, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 32 :=
  ⟨⟨60,19,96⟩,mass_cell 32 60 19 96 158 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 963400027314, 405212887554, 69652548842, 3307276562, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 32 :=
  ⟨⟨89,15,96⟩,mass_cell 32 89 15 96 170 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 963448304324, 406496819637, 68413521601, 2030429758, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 32 :=
  ⟨⟨89,24,98⟩,mass_cell 32 89 24 98 150 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 427803872255, 45078987087, 480088294, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 32 :=
  ⟨⟨102,51,101⟩,mass_cell 32 102 51 101 128 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 464130318168, 9737650709, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 32 :=
  ⟨⟨74,21,97⟩,mass_cell 32 74 21 97 154 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 414212789568, 57785725904, 1565609220, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 32 :=
  ⟨⟨83,31,99⟩,mass_cell 32 83 31 99 141 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 441664001887, 31997732713, 26483392, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 32 :=
  ⟨⟨100,38,100⟩,mass_cell 32 100 38 100 135 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 453523655329, 20257735251, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 32 :=
  ⟨⟨112,50,101⟩,mass_cell 32 112 50 101 128 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 464009298352, 10015769512, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 32 :=
  ⟨⟨118,36,100⟩,mass_cell 32 118 36 100 137 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 453122280420, 20723108427, 26798, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 32 :=
  ⟨⟨96,18,97⟩,mass_cell 32 96 18 97 162 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 414775231538, 56586460758, 923599576, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 32 :=
  ⟨⟨109,28,99⟩,mass_cell 32 109 28 99 145 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 440884757808, 32474617538, 58213416, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 32 :=
  ⟨⟨112,15,97⟩,mass_cell 32 112 15 97 171 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 419147797726, 52887202032, 10334640, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 32 :=
  ⟨⟨122,49,101⟩,mass_cell 32 122 49 101 129 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 463803073761, 10238666455, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 32 :=
  ⟨⟨120,3,95⟩,mass_cell 32 120 3 95 259 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 957486969759, 430422193806, 52709419422, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 32 :=
  ⟨⟨126,6,96⟩,mass_cell 32 126 6 96 221 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 964239518450, 428949678085, 48160058785, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 32 :=
  ⟨⟨110,21,98⟩,mass_cell 32 110 21 98 155 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 428902553554, 44028869842, 139336141, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 32 :=
  ⟨⟨131,17,98⟩,mass_cell 32 131 17 98 165 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 433572224888, 39058759570, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 32 :=
  ⟨⟨126,35,100⟩,mass_cell 32 126 35 100 138 (by decide)
    (by decide +kernel) [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 453163540937, 20844510814, 184239, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 32) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39]

end Low6969Allocation.Group32
end Z6969Source2382

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles32
section Z6969Source2383
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group32
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27854048263, 40824612883, 87046377503, 44449375291, 39617319219, 30960417075], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39214881075, 13143163299, 17572338107, 13176712635, 8831417787, 1099736402403], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099736403427, 4368678391, 1099652515319, 34483408379, 8663641603, 4351900163], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25826654731, 17236792843, 1099568562699, 23378451, 23379475, 4301565463], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301567511], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 133 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36461877259, 61578361879, 86979475499, 1751436359, 30926862639, 34919913775], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17807228207, 43627068787, 30759086451, 17522006455, 8915299767, 8814639543], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099853776327, 1099853842887, 1099702849003, 1099686001135, 1099686002159, 1099686003183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17287055871, 43039857155, 4368674311, 73709063, 8646860299, 4351896075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38661146135], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 133 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40757371919, 65756089375, 69850008627, 26447416643, 22035081539, 13411598659], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39415991647, 26548008287, 1099870552515, 1099870553539, 1099870620099, 1099870621123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8814635467, 4486116811, 1099836997067, 17354232295, 8747525607, 1099635668475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099635669499, 90485251, 43023083015, 4335117839, 40152591, 12908270099], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8613306899, 38661149207], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 133 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40824746003, 69916907555, 52754095159, 35255310659, 26548010307, 26296424771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17572345179, 4737780059, 4519671227, 1099904105915, 1099904106939, 1099904107963], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13193484739, 8814635459, 1099853842887, 1099853843911, 1099669222899, 1099669223923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4385450491, 1099635667451, 21582020095, 12992157183, 4335117839, 23375379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44918586391, 69849868327, 35658116159, 31010744631, 26480970039, 22035080503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13126385015, 1100189322615, 1099937660339, 1099937661363, 1099937662387, 1099937663411], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8864966079, 4519670207, 1099887327679, 17404496355, 8814632419, 43123817967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652444663, 1099652445687, 90483203, 90484227], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44868388891, 65554969643, 27101738047, 26682225979, 22169227579, 21951195451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8814641535, 1100155768191, 8864967087, 4519671215, 1099954437551, 1099920884151], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920885175, 1099920886199, 13109596643, 8747524579, 38862408167, 25977647591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719554535, 1099719555559, 157593075, 1099669221875, 4351894027, 56928779], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12891491863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48928543775, 65471153199, 10056156231, 22404105515, 22102121771, 21900866859], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8831415699, 1100071879059, 1099987994023, 1099987995047, 1099988061607, 39046960563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21900787123, 8948850115, 4586777027, 4486115779, 1099820218831, 1099820219855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669221875, 1099669222899, 8646858251, 56928779, 56929803, 38677927443], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57233399843, 56881289271, 22102120755, 17673007411, 9049523507, 35054051699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22118892915, 1100004771235, 1100004772259, 1100004838819, 4586779051, 1099971213739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971214763, 1099971215787, 8915295691, 4569999819, 1099669221875, 1099669222899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17219945999, 8630082063, 40151567, 40152591], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61343820839, 39835641915, 30926859595, 22186003787, 17706558795, 13227047255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100323539287, 1100323540311, 1099971213739, 1099971214763, 1099971215787, 1099971216811], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8814634443, 4452561355, 1099669221875, 1099669222899, 13025644023, 8730746359], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [90483203, 90484227], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52871395371, 35557452863, 13344484703, 13159939423, 1100289985887, 26497677675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17773598059, 13344483691, 1100004769187, 1100004770211, 1100004771235, 1100004772259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820218831, 4519668187, 1099769885147, 1099769886171, 13008934395, 4419003899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23375379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [56998659119, 18562202691, 22353773895, 17823931719, 17605898567, 1100088657295], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088658319, 1100088659343, 4603556271, 1099954436527, 1099954437551, 1099954438575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8814632419, 4502890979, 1099635667451, 1099635668475, 6597143, 6598167], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61125857331, 1533332551, 26514526499, 22001528099, 9116632355, 8898522531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4536449443, 1100004770211, 1100004771235, 1100004772259, 1099920952759, 17421275607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8814634455, 1099753109983, 1099753111007, 174371311, 1099686000111, 4335117839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [40152591, 17203237395], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52603100215, 22102121783, 17639454007, 4788111671, 4603557287, 1099987991975], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987992999, 1099987994023, 1099954440623, 1099954507183, 13159931343, 4553223631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099669222899, 1099669223923, 40152591, 40153615, 8613305875, 4318341651], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 32 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group32
end Z6969Source2383

-- Source: ProximityPrize.SubmissionLower.Low6969Mass33
section Z6969Source2384
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group33

private def m0 : MassCell 33 :=
  ⟨⟨1,3,74⟩,mass_cell 33 1 3 74 238 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1139302609135, 775997339723, 504117496711, 307997896099, 173203689887, 86530366075, 36003748663, 10879997651, 1645609039, 26763790, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 33 :=
  ⟨⟨2,6,90⟩,mass_cell 33 2 6 90 215 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 871281814590, 519260443109, 275249236709, 125534573637, 44676670277, 9802120229, 603894309, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 33 :=
  ⟨⟨3,9,97⟩,mass_cell 33 3 9 97 199 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 562832478564, 261707563908, 96138170788, 22493543364, 1672774116, 8408, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 33 :=
  ⟨⟨1,10,98⟩,mass_cell 33 1 10 98 194 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 572928907157, 257094712485, 87900134957, 17310988589, 724445815, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 33 :=
  ⟨⟨4,12,101⟩,mass_cell 33 4 12 101 186 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 606765962258, 255520597525, 74953150661, 10359944701, 107150692, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 33 :=
  ⟨⟨1,15,103⟩,mass_cell 33 1 15 103 177 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 626803567622, 248009212651, 57371615239, 3921626627, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 33 :=
  ⟨⟨1,18,105⟩,mass_cell 33 1 18 105 170 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 647019439598, 249215291057, 45411577041, 1379564835, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 33 :=
  ⟨⟨1,20,106⟩,mass_cell 33 1 20 106 166 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 655934964400, 250152564324, 38659625400, 597232194, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 33 :=
  ⟨⟨1,23,107⟩,mass_cell 33 1 23 107 161 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 663508329487, 247602111997, 29215299289, 102127659, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 33 :=
  ⟨⟨1,26,108⟩,mass_cell 33 1 26 108 157 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 669891350993, 251574608363, 23039794787, 7149679, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 33 :=
  ⟨⟨1,30,109⟩,mass_cell 33 1 30 109 152 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 256617836780, 16665147216, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 33 :=
  ⟨⟨1,36,110⟩,mass_cell 33 1 36 110 147 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 261978024166, 9910802710, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 33 :=
  ⟨⟨9,43,111⟩,mass_cell 33 9 43 111 143 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 269250890637, 5530474956, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 33 :=
  ⟨⟨65,30,110⟩,mass_cell 33 65 30 110 153 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 260970506018, 13809000734, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 33 :=
  ⟨⟨68,38,111⟩,mass_cell 33 68 38 111 146 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 267605944487, 7345640867, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 33 :=
  ⟨⟨75,29,110⟩,mass_cell 33 75 29 110 154 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 260402691108, 14107196100, 380032, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 33 :=
  ⟨⟨53,21,108⟩,mass_cell 33 53 21 108 165 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 669648012827, 249253481318, 28950427638, 338081435, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 33 :=
  ⟨⟨78,37,111⟩,mass_cell 33 78 37 111 147 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 267408827006, 7644654820, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 33 :=
  ⟨⟨62,20,108⟩,mass_cell 33 62 20 108 168 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 669622507430, 248685948549, 29299283037, 432101238, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 33 :=
  ⟨⟨46,26,109⟩,mass_cell 33 46 26 109 158 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 254391814240, 20519421388, 16748088, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 33 :=
  ⟨⟨76,50,112⟩,mass_cell 33 76 50 112 139 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 272270319143, 2629766378, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 33 :=
  ⟨⟨74,23,109⟩,mass_cell 33 74 23 109 163 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 253019167040, 21871415360, 93400300, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 33 :=
  ⟨⟨88,36,111⟩,mass_cell 33 88 36 111 148 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 267077258695, 7866557220, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 33 :=
  ⟨⟨97,48,112⟩,mass_cell 33 97 48 112 141 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 272031330787, 2928942684, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 33 :=
  ⟨⟨95,15,108⟩,mass_cell 33 95 15 108 182 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 669710977710, 250744106975, 27106145358, 1837620, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 33 :=
  ⟨⟨99,26,110⟩,mass_cell 33 99 26 110 159 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 260392433273, 14612877449, 3735863, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 33 :=
  ⟨⟨89,21,109⟩,mass_cell 33 89 21 109 166 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 253111815620, 21816937540, 75493003, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 33 :=
  ⟨⟨107,47,112⟩,mass_cell 33 107 47 112 141 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 271895847376, 3056672710, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 33 :=
  ⟨⟨107,18,109⟩,mass_cell 33 107 18 109 174 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 254714240991, 19918215296, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 33 :=
  ⟨⟨117,46,112⟩,mass_cell 33 117 46 112 142 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 271676173606, 3154839511, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 33 :=
  ⟨⟨120,9,108⟩,mass_cell 33 120 9 108 210 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 670082632186, 258803951730, 18211338093, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 33 :=
  ⟨⟨97,35,111⟩,mass_cell 33 97 35 111 149 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 266946447877, 8067593765, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 33 :=
  ⟨⟨122,32,111⟩,mass_cell 33 122 32 111 152 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 266501072816, 8137307419, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 33 :=
  ⟨⟨126,45,112⟩,mass_cell 33 126 45 112 142 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 271600856633, 3245869911, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 33 :=
  ⟨⟨121,15,109⟩,mass_cell 33 121 15 109 183 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 257687350951, 16880407366, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 33 :=
  ⟨⟨129,21,110⟩,mass_cell 33 129 21 110 167 (by decide)
    (by decide +kernel) [4447931157624, 3676614856324, 3008776416168, 2434915300068, 1945974313528, 1533339604644, 1188840664104, 904750325188, 673784763768, 262443358224, 12433117526, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 33) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35]

end Low6969Allocation.Group33
end Z6969Source2384

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles33
section Z6969Source2385
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group33
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27955694599, 44952594451, 87080719391, 40205461563, 43778856251, 35121955131], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39165338939, 1099921673647, 17505953207, 13127104951, 4587571639, 43074202099], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25894552051, 17304624627, 8681208307, 4369466867, 38712202755, 25827376643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8630809095, 40945159, 1099552573959, 4319133195], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i51 : checks (tilesOf batches) 131 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36529903627, 57451953175, 86996972587, 6047123527, 35205838131, 34971031859], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17824726323, 43443305883, 34853513627, 17489172935, 8882466247, 8781806023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4470130127, 1099670015467, 4403018231, 108052983, 1099602904571, 1099602905595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21549256191, 4302286351, 4302353935], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i46 : checks (tilesOf batches) 131 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44935750671, 74246148127, 57116891191, 39500665159, 30860540231, 22035798379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21851255147, 4805675371, 8815358407, 4520459719, 4453352903, 1099686792679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43107755499, 1099653236207, 1099653237231, 13009656307, 8697915891, 4369462783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [74497535, 1099586126335, 25810598407, 17220736519, 4302285327, 4302287375], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 131 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45036679187, 65756945443, 52805147703, 39349738851, 26414581091, 17757610343], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17573066087, 4788898151, 4537169351, 4486905287, 1099821008327, 1099720346079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099720347103, 8714691059, 4419726835, 1099619679735, 1099619680759, 21549254143], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12959325695, 57718275, 57719299, 42990318087, 38678715915], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [45020036119, 69917763623, 35742788671, 35172215111, 26448137543, 22002248007], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13110395275, 1099837784515, 1099837785539, 1099837786563, 1099837787587, 8848910791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4520392135, 4470128071, 17338174955, 8748245483, 1099636456947, 74495487], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [74496511, 42990386695, 4335840775, 34383751691], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49113810971, 82567854123, 5912905799, 31078643987, 26565646611, 26313995539], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8916022679, 8815427991, 1099804233163, 1099787452879, 1099787453903, 1099787454927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13143874003, 8798579155, 43174939099, 30290114011, 175093223, 175159783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099686788583, 12925769223, 4335839751, 40874503], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53207520287, 69750065203, 1651493959, 26615908651, 26347545899, 13445873963], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43325937071, 26162921903, 4486906291, 1099904895411, 8966350263, 4637831607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4520393143, 1099770678739, 1099703566819, 1099703567843, 141605359, 1099653234159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12992880119, 42973681163, 24097291, 24163851, 25777111567], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53140480035, 61210530871, 22270678331, 21985471803, 9117353275, 39114858915], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21935065507, 8882466231, 4537170359, 1099888116151, 1099871339963, 1099871340987], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099871342011, 124828147, 1099636456947, 8681136635, 4369395199, 74495487], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61462047783, 39920248891, 35071552871, 22153236839, 17640171883, 13210991979], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100206886251, 4503682491, 1099871339963, 1099871340987, 8798579163, 4453283291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099653234159, 1099653235183, 57718275, 57719299, 17203958283, 8614028811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [7320079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61395007531, 27186410559, 30826985819, 22119684443, 17623396699, 4587570579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100039114131, 4604277191, 4486838727, 1099821007303, 1099737122267, 1099737123291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17287846391, 4402949623, 108050935, 1099619679735], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61311124527, 14418952259, 30793434443, 17858274635, 17606621515, 4587502003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4520460723, 1099904895411, 1099904896435, 1099670012395, 1099670013419, 12992882159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4386174447, 25860998651, 12976103931, 1099602902523, 4335908359, 4319064587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65471942707, 26582356271, 22069357871, 9184462127, 8916020671, 4553947583], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4470129087, 1099854563775, 1099854564799, 1099670012395, 1099670013419, 21599588851], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8714693107, 74496511, 74497535, 4302353935], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52704484407, 22170017103, 17656952143, 4856006991, 4621055427, 4537236931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099837785539, 1099753900503, 1099753901527, 17287847415, 4402950647, 74497535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099586126335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((33 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 33 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group33
end Z6969Source2385

-- Source: ProximityPrize.SubmissionLower.Low6969Mass34
section Z6969Source2386
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group34

private def m0 : MassCell 34 :=
  ⟨⟨1,3,85⟩,mass_cell 34 1 3 85 249 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 826316924788, 540814838092, 334187275556, 191284169980, 98351678164, 43032180908, 14364283012, 2782813276, 118961293, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 34 :=
  ⟨⟨2,6,100⟩,mass_cell 34 2 6 100 225 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 604163279404, 333802532299, 161321220339, 63697641459, 17461183819, 2072068731, 9972741, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 34 :=
  ⟨⟨1,9,106⟩,mass_cell 34 1 9 106 208 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 637863832946, 348173577036, 144022088748, 42648891148, 6030242796, 69360362, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 34 :=
  ⟨⟨4,10,108⟩,mass_cell 34 4 10 108 204 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 644264259107, 359544890090, 139998907638, 37299915578, 4094565686, 11779296, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 34 :=
  ⟨⟨2,12,110⟩,mass_cell 34 2 12 110 195 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 375720698602, 133412586806, 28835882674, 1662738334, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 34 :=
  ⟨⟨1,15,112⟩,mass_cell 34 1 15 112 186 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 391131693931, 121556219066, 18184011658, 257172511, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 34 :=
  ⟨⟨1,18,114⟩,mass_cell 34 1 18 114 179 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 410546565068, 117054766381, 12195166381, 18348254, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 34 :=
  ⟨⟨5,20,115⟩,mass_cell 34 5 20 115 175 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 418951875579, 112059236805, 8882556909, 367320, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 34 :=
  ⟨⟨4,23,116⟩,mass_cell 34 4 23 116 170 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 427740077260, 106638889937, 5556414347, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 34 :=
  ⟨⟨1,27,117⟩,mass_cell 34 1 27 117 164 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 436472217890, 100681719856, 2866183759, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 34 :=
  ⟨⟨1,32,118⟩,mass_cell 34 1 32 118 159 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 444876867231, 94347201122, 1134132385, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 34 :=
  ⟨⟨3,39,119⟩,mass_cell 34 3 39 119 153 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 452826677379, 87264759116, 222149876, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 34 :=
  ⟨⟨1,50,120⟩,mass_cell 34 1 50 120 147 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 460067870064, 80263396027, 751778, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 34 :=
  ⟨⟨13,26,117⟩,mass_cell 34 13 26 117 166 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 436076187765, 100923180516, 3345074944, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 34 :=
  ⟨⟨62,34,119⟩,mass_cell 34 62 34 119 158 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 452177124816, 87408496171, 665075806, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 34 :=
  ⟨⟨68,26,118⟩,mass_cell 34 68 26 118 167 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 443596434025, 93994100624, 2491886578, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 34 :=
  ⟨⟨27,48,120⟩,mass_cell 34 27 48 120 149 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459949076175, 80386730504, 7206004, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 34 :=
  ⟨⟨73,20,117⟩,mass_cell 34 73 20 117 177 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 434625406444, 99920983041, 5199555609, 776220, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 34 :=
  ⟨⟨73,44,120⟩,mass_cell 34 73 44 120 151 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459774979663, 80575311987, 51307813, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 34 :=
  ⟨⟨72,33,119⟩,mass_cell 34 72 33 119 159 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 452100130202, 87381001376, 760490172, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 34 :=
  ⟨⟨80,19,117⟩,mass_cell 34 80 19 117 179 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 434680661434, 100024012599, 5096861365, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 34 :=
  ⟨⟨84,24,118⟩,mass_cell 34 84 24 118 170 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 443546591293, 94148558737, 2703684569, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 34 :=
  ⟨⟨94,42,120⟩,mass_cell 34 94 42 120 152 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459708032638, 80446818428, 88123013, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 34 :=
  ⟨⟨104,21,118⟩,mass_cell 34 104 21 118 175 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 443717895942, 94373618402, 2232059802, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 34 :=
  ⟨⟨90,31,119⟩,mass_cell 34 90 31 119 161 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 452009642730, 87378045733, 916819708, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 34 :=
  ⟨⟨103,41,120⟩,mass_cell 34 103 41 120 153 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459692547994, 80524806208, 108507648, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 34 :=
  ⟨⟨86,18,117⟩,mass_cell 34 86 18 117 182 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 434847586919, 100415452023, 4850819612, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 34 :=
  ⟨⟨106,29,119⟩,mass_cell 34 106 29 119 163 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 451981672385, 87295195326, 954428644, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 34 :=
  ⟨⟨112,40,120⟩,mass_cell 34 112 40 120 154 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459676395775, 80500490793, 126528507, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 34 :=
  ⟨⟨102,15,117⟩,mass_cell 34 102 15 117 191 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 435540151330, 101177023897, 3173861474, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 34 :=
  ⟨⟨120,39,120⟩,mass_cell 34 120 39 120 154 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459672477400, 80589930011, 141980998, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 34 :=
  ⟨⟨115,12,117⟩,mass_cell 34 115 12 117 202 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 436547300484, 101594118821, 1342845557, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 34 :=
  ⟨⟨120,18,118⟩,mass_cell 34 120 18 118 183 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 444145878306, 94575526988, 1130391389, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 34 :=
  ⟨⟨120,27,119⟩,mass_cell 34 120 27 119 166 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 452018911156, 87192820265, 786795388, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 34 :=
  ⟨⟨128,38,120⟩,mass_cell 34 128 38 120 155 (by decide)
    (by decide +kernel) [4439132330535, 3654964629767, 2978566323095, 2399713012503, 1908680542151, 1496244998375, 1153682709687, 872770246775, 645784422503, 459667984201, 80575091781, 148776000, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 34) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34]

end Low6969Allocation.Group34
end Z6969Source2386

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles34
section Z6969Source2387
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group34
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27939638279, 40775723027, 87014199327, 44383577147, 39585141035, 30911396139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34938001707, 17389108627, 13245061559, 13144467895, 8799173047, 1099804755399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099804756423, 1099804757447, 1099653757419, 1099653758443, 1099653759467, 25861519863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12976625143, 4386761207, 4369986039, 38662459915, 7909899, 7910923], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36513781771, 44886408215, 86947162151, 18714442819, 35239913763, 30777249059], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34820566307, 13211577747, 4520983987, 1099888641459, 1099888642483, 1099888643507], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17439362511, 8849498575, 4453871075, 4386764259, 38813384167, 30223525351], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099653758443, 1099653759467, 17271588343, 75019771, 1099586648571, 7908875], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [7909899], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40792368143, 65723845663, 69834542131, 26415172927, 26213853503, 9134720319], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39417367895, 26532541783, 8916609451, 8799172011, 1099922194859, 1099821532611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099821533635, 1099821534659, 13094064603, 8799166939, 1099704088031, 1099704089055], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099704090079, 4336430587, 24686087, 24687111], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44953382931, 69918284835, 48477216827, 35206290755, 26482213187, 22036323651], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17523324259, 4688759139, 4520981943, 1099871862199, 1099871863223, 1099871864247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099821533635, 1099821534659, 8866209227, 4571310539, 4487426507, 21600109039], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8715213295, 1099636980207, 43058016755, 75018747, 1099586647547], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44953517079, 82568308775, 22875191363, 31129430287, 30844356879, 30592706831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13211576719, 8832727443, 1100022859155, 1100022860179, 1100022861203, 17456138699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8866209227, 1099771197903, 1099771198927, 1099771199951, 4487424479, 192459231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099704088031, 43041242615], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53208041499, 69767363631, 14352367683, 26649984299, 22170540331, 26197143851], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8916611475, 8782396819, 1099955751331, 1099955752355, 43343235499, 30424921515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099821530563, 1099821531587, 1099821532611, 13094066643, 4537756115, 175682019], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099687310819, 1099687311843, 12943070719, 25811187203, 12926292483, 4319651335], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42957425163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53157778463, 69717100595, 1601752135, 26599721251, 26297738531, 13429686563], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39098668451, 26213842339, 13194798499, 8799172003, 1099938972071, 1099938973095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099938974119, 1099804757447, 1099737642455, 1099737643479, 1099737644503, 13010180587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4420315631, 125350383, 12892805643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57285042211, 56899311671, 22153763127, 17724649783, 9101165879, 39216111999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22053095807, 1099888641459, 1099888642483, 1099888643507, 4571312571, 4470651323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099855086011, 8799166939, 4487425499, 1099670534631, 1099670535655, 1099569870335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34384273927, 21499446791, 8597839371, 7908875, 7909899], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61429083175, 39904061499, 35072142687, 22103429471, 17590364519, 13194804583], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100207410535, 1099888639411, 1099888640435, 1099888641459, 1099888642483, 8815946187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4470650315, 17271591415, 8681727479, 91796983, 1099603425783, 41464323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34367565323], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61345200171, 27119825983, 30844287311, 22086654287, 17640763727, 8799176067], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099871864247, 1099871865271, 1099871866295, 4604867007, 4487428543, 1099838308799], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13060512227, 8748837347, 1099636980207, 1099636981231, 30072601099, 4302875147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [7909899, 7910923], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61294937135, 14369144899, 26599720263, 22053101895, 17590434119, 1099938975143], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4588091819, 1099922194859, 1099922195883, 1099922196907, 13127688659, 4537758163], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [108575219, 1099620204019], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61211054131, 1635306567, 26532614455, 21985996087, 9134720311, 8933387699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4571314611, 1099888640435, 1099855087035, 1099855088059, 1099771203023, 21583335919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8715282927, 91798007, 1099603426807, 24688135, 17187705355, 8597841419], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52688297015, 22120209739, 17657541963, 4822976843, 4604868031, 4487429567], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099838309823, 1099787979211, 1099787980235, 17338768871, 4453872103, 1099636981231], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099636982255, 7911947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 34 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group34
end Z6969Source2387

-- Source: ProximityPrize.SubmissionLower.Low6969Mass35
section Z6969Source2388
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group35

private def m0 : MassCell 35 :=
  ⟨⟨1,3,102⟩,mass_cell 35 1 3 102 266 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 605295355012, 384112409995, 225681754447, 120793223219, 56469363511, 21294834523, 5416407455, 542965507, 901188, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 35 :=
  ⟨⟨1,6,115⟩,mass_cell 35 1 6 115 240 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 427882646973, 229743657786, 102774391062, 35646538282, 7503174006, 418205946, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 35 :=
  ⟨⟨3,9,121⟩,mass_cell 35 3 9 121 223 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 246333831384, 92235585112, 22873019352, 2088743256, 1286898, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 35 :=
  ⟨⟨1,10,122⟩,mass_cell 35 1 10 122 218 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 251844532249, 90066156585, 19965284769, 1269281281, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 35 :=
  ⟨⟨1,12,124⟩,mass_cell 35 1 12 124 209 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 262490038249, 85632527238, 14814677594, 400830498, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 35 :=
  ⟨⟨1,15,126⟩,mass_cell 35 1 15 126 200 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 272763539488, 79408774659, 9105194447, 31054519, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 35 :=
  ⟨⟨1,17,127⟩,mass_cell 35 1 17 127 194 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 277977331971, 75988461572, 6502313348, 1111622, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 35 :=
  ⟨⟨1,19,128⟩,mass_cell 35 1 19 128 190 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 283739317065, 74482198315, 4814655183, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 35 :=
  ⟨⟨1,22,129⟩,mass_cell 35 1 22 129 184 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 288916655445, 70957003932, 2871909468, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 35 :=
  ⟨⟨1,26,130⟩,mass_cell 35 1 26 130 179 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 293943630423, 67029709067, 1368568632, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 35 :=
  ⟨⟨1,31,131⟩,mass_cell 35 1 31 131 173 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 298834224771, 64158743163, 501091007, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 35 :=
  ⟨⟨1,39,132⟩,mass_cell 35 1 39 132 166 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 303028526020, 59902082579, 51356091, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 35 :=
  ⟨⟨11,50,133⟩,mass_cell 35 11 50 133 160 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57778076803, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 35 :=
  ⟨⟨65,33,132⟩,mass_cell 35 65 33 132 172 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302878423854, 60760931536, 280435166, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 35 :=
  ⟨⟨36,48,133⟩,mass_cell 35 36 48 133 162 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57806562178, 137354, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 35 :=
  ⟨⟨61,20,130⟩,mass_cell 35 61 20 130 190 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 293312564956, 67566269538, 2757549726, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 35 :=
  ⟨⟨57,26,131⟩,mass_cell 35 57 26 131 180 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 298411653365, 64106667285, 1130624486, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 35 :=
  ⟨⟨75,32,132⟩,mass_cell 35 75 32 132 173 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302857341086, 60675047563, 322675621, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 35 :=
  ⟨⟨48,47,133⟩,mass_cell 35 48 47 133 162 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57800087796, 858420, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 35 :=
  ⟨⟨69,19,130⟩,mass_cell 35 69 19 130 192 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 293288312979, 67485203453, 2790388481, 9796, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 35 :=
  ⟨⟨71,45,133⟩,mass_cell 35 71 45 133 163 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57736687436, 5021064, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 35 :=
  ⟨⟨74,24,131⟩,mass_cell 35 74 24 131 183 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 298367749814, 64200427094, 1311630204, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 35 :=
  ⟨⟨81,44,133⟩,mass_cell 35 81 44 133 164 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57785169600, 8637142, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 35 :=
  ⟨⟨91,43,133⟩,mass_cell 35 91 43 133 165 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57782376839, 13283080, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 35 :=
  ⟨⟨93,15,130⟩,mass_cell 35 93 15 130 204 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 293583481043, 68122285201, 1920265103, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 35 :=
  ⟨⟨96,21,131⟩,mass_cell 35 96 21 131 188 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 298382104859, 64102695550, 1161507746, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 35 :=
  ⟨⟨84,31,132⟩,mass_cell 35 84 31 132 174 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302845097750, 60660936698, 360525969, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 35 :=
  ⟨⟨101,42,133⟩,mass_cell 35 101 42 133 165 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57722358485, 18568609, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 35 :=
  ⟨⟨112,18,131⟩,mass_cell 35 112 18 131 196 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 298550790782, 64551772338, 631601418, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 35 :=
  ⟨⟨101,29,132⟩,mass_cell 35 101 29 132 176 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302828511589, 60491776878, 389548803, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 35 :=
  ⟨⟨110,41,133⟩,mass_cell 35 110 41 133 166 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57721885282, 24144352, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 35 :=
  ⟨⟨106,12,130⟩,mass_cell 35 106 12 130 215 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 294052401411, 68877694749, 886531604, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 35 :=
  ⟨⟨118,40,133⟩,mass_cell 35 118 40 133 167 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57789462198, 29519560, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 35 :=
  ⟨⟨114,10,130⟩,mass_cell 35 114 10 130 226 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 294391520986, 68821135458, 323469867, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 35 :=
  ⟨⟨108,28,132⟩,mass_cell 35 108 28 132 178 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302833833100, 60554434087, 377646294, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 35 :=
  ⟨⟨126,39,133⟩,mass_cell 35 126 39 133 167 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 306092914566, 57801159412, 33003358, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 35 :=
  ⟨⟨126,25,132⟩,mass_cell 35 126 25 132 182 (by decide)
    (by decide +kernel) [4430333503446, 3633314403210, 2948356230022, 2364510724938, 1871386770774, 1459150392106, 1118524755270, 840790168362, 617784081238, 441901085514, 302876566882, 60828972734, 209106153, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 35) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36]

end Low6969Allocation.Group35
end Z6969Source2388

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles35
section Z6969Source2389
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group35
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27923975175, 40692754451, 86947942431, 44300543035, 35358134555, 30912247067], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39183488283, 13162102143, 1100090822015, 13296244123, 13162030491, 8850355611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099805606339, 1099805607363, 1099805608387, 1099704939995, 1099704941019, 1099704942043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4471498207, 4404391391, 21617735143, 13027806695, 38713567739, 59092475], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099570721275, 8632245759], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36497987595, 48964189207, 86914526247, 14386774083, 30962576667, 34955627803], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26298593563, 8867131803, 8766471579, 17507323307, 8900616619, 8833576363], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099906271659, 1099906272683, 39015562675, 30408926643, 1099788828103, 1099788829127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099788830151, 1099688163807, 4370836967, 1099654608359, 17272440307, 4370833911], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4337281527, 8648956411, 1099570721275, 25537027, 25538051, 30073447943], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40776573967, 69919067167, 65523650611, 26348917051, 21919739195, 9102017851], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39451774271, 26566948159, 8833576359, 8732916135, 1099855938999, 1099855940023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099855941047, 13162025415, 8783176135, 1099772049867, 1099772050891, 1099772051915], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [159755747, 1099671384547, 1099671385571, 4370833911, 4337281527, 34401897983], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25812038143, 12927143423, 25537027], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44920746003, 69885582371, 48444514363, 35190365499, 26499907899, 22037175611], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17524176219, 4689611099, 4521833903, 1099889491375, 1099889492399, 1099889493423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099839162811, 1099839163835, 8867061187, 8766466499, 1099654608359, 1099654609383], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43075645931, 21584183787, 8716065259, 4370835951, 1099621052911, 34385124867], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25537027, 25538051, 17188553223, 8598623751, 4303726087], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44937657367, 78324590631, 27137455167, 31063238939, 26567018779, 30543226139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100057265543, 1100057266567, 1100057267591, 13195584911, 8867132815, 1100023710095], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099738494419, 1099738495443, 1099738496467, 17373104603, 8783175131, 4471499227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [193311195, 43042094579, 8759815, 8760839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49031366683, 65557133355, 22859266115, 26634058043, 22137836859, 21902961979], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100023711119, 1100023712143, 1100023713167, 8883908003, 4538612131, 1099939824035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43226712519, 26046920135, 13078140379, 8749688283, 1099688163807, 1099688164831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [126202347, 1099637831147, 4320503299, 25538051], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48981103647, 78224000047, 30912316683, 26399253771, 13531201803, 8967726499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8850354595, 4521835939, 1099923047847, 1099923048871, 1099923049895, 38965302719], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26080476607, 13094918615, 1099704942043, 1099704943067, 4387615203, 1099671386595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [59093499, 59094523, 4337281535], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53108367395, 61161575479, 26432804143, 21936517423, 4890937647, 39099523483], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21936507291, 8900686239, 4555390367, 1099956602271, 1099822385599, 1099822386623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8833507791, 4538609103, 1099688164831, 1099688165855, 126203371, 1099637832171], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34368348679, 21483521543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61446712359, 39921690683, 35056217443, 22121058659, 17591216491, 13195656555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100174708075, 4471504311, 1099855938999, 1099855940023, 8833575375, 4488279503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099671387619, 1099671388643, 17222111743, 8632247807, 42317311, 42318335], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [57168525355, 31398867007, 30727698795, 17826093419, 13380136299, 8934243711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4588947839, 1099788831175, 1099788832199, 1099738496467, 1099738497491, 1099738498515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8716135907, 159758819, 4320505347, 25540099, 12893592071, 8598694407], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65540424751, 10142139463, 30861985083, 22087509307, 17641618747, 4572167595], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099839161787, 1099839162811, 1099839163835, 13128541647, 4538611151, 109428207], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099621057007, 25828820475, 12943991291], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [57017602099, 5947902023, 26483134799, 17742212431, 13329875279, 4488282555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099738499539, 1099738500563, 8800021975, 4471503319, 1099637834219, 1099637835243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21533856251, 8649026043, 25541123, 25542147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52739480631, 22121061719, 17658393943, 4823828823, 8800024011, 4437950923], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099721722327, 1099721723351, 109429231, 1099621058031, 17272446451, 8682582515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42319359], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((35 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 35 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group35
end Z6969Source2389

-- Source: ProximityPrize.SubmissionLower.Low6969Mass36
section Z6969Source2390
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group36

private def m0 : MassCell 36 :=
  ⟨⟨1,3,143⟩,mass_cell 36 1 3 143 307 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 188553675114, 104912249920, 48352221440, 17979060160, 4527230080, 459195200, 998100, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 36 :=
  ⟨⟨1,6,152⟩,mass_cell 36 1 6 152 277 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 114820544503, 46997639220, 12568630848, 1453277308, 6813865, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 36 :=
  ⟨⟨1,9,156⟩,mass_cell 36 1 9 156 258 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118083716345, 48287782638, 9289859582, 393324951, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 36 :=
  ⟨⟨1,10,157⟩,mass_cell 36 1 10 157 253 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 49340683002, 8548574014, 248118106, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 36 :=
  ⟨⟨1,12,158⟩,mass_cell 36 1 12 158 243 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 49654185761, 6756763489, 68841634, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 36 :=
  ⟨⟨4,15,160⟩,mass_cell 36 4 15 160 234 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 52899550743, 5474268857, 8454933, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 36 :=
  ⟨⟨4,18,161⟩,mass_cell 36 4 18 161 226 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 54049234797, 4285050407, 22282, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 36 :=
  ⟨⟨1,23,162⟩,mass_cell 36 1 23 162 216 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 54925944751, 2868564480, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 36 :=
  ⟨⟨1,29,163⟩,mass_cell 36 1 29 163 207 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 56200893419, 1933133088, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 36 :=
  ⟨⟨1,39,164⟩,mass_cell 36 1 39 164 198 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 57342053076, 1036431525, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 36 :=
  ⟨⟨67,23,163⟩,mass_cell 36 67 23 163 217 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 56028685117, 2361675679, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 36 :=
  ⟨⟨64,34,164⟩,mass_cell 36 64 34 164 203 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 57180399478, 1236067544, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 36 :=
  ⟨⟨84,21,163⟩,mass_cell 36 84 21 163 220 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 56027743846, 2397358266, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 36 :=
  ⟨⟨85,32,164⟩,mass_cell 36 85 32 164 205 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 57138581872, 1287150644, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 36 :=
  ⟨⟨61,17,162⟩,mass_cell 36 61 17 162 229 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 54838532811, 3549265232, 721880, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 36 :=
  ⟨⟨104,30,164⟩,mass_cell 36 104 30 164 207 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 57107906890, 1307792611, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 36 :=
  ⟨⟨113,51,165⟩,mass_cell 36 113 51 165 192 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 58029376208, 392483114, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 36 :=
  ⟨⟨119,6,162⟩,mass_cell 36 119 6 162 287 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 55902483474, 2422894242, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 36 :=
  ⟨⟨124,50,165⟩,mass_cell 36 124 50 165 192 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 58015714008, 400766581, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 36 :=
  ⟨⟨121,15,163⟩,mass_cell 36 121 15 163 237 (by decide)
    (by decide +kernel) [4421534676357, 3611664176653, 2918146136949, 2329308437373, 1834092999397, 1422055785837, 1083366800853, 808810089949, 589783739973, 418299879117, 286984676917, 189078344253, 118435133349, 56307708992, 2070832625, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 36) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19]

end Low6969Allocation.Group36
end Z6969Source2390

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles36
section Z6969Source2391
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group36
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [32204852231, 49251429395, 87151500323, 31753285695, 43715353935, 35075164495], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30645988687, 212192723, 17358433755, 8768504283, 47322377715, 30109108731], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17224215035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
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
private theorem i51 : checks (tilesOf batches) 128 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [44939352075, 65995293723, 78595195951, 35041609059, 30595656035, 4976855395], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47725036947, 39135180179, 21619845603, 12996362723, 43077736935, 8617509375], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i46 : checks (tilesOf batches) 128 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [49352025103, 78645384223, 48798933051, 47943210335, 39303021919, 21821173167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8953054639, 34404075003, 21519182331, 8600732163], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i49 : checks (tilesOf batches) 128 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [53613572115, 78628676647, 31803617343, 47926437219, 35008058723, 17341659615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [161861087, 30092334591, 17207440895, 51550237187], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [57841564695, 87084463147, 6168037447, 43748914503, 35058393415, 9389262151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25864479215, 17274551791, 55895604727], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57875187739, 78578417711, 1873071175, 43648319839, 30679543135, 25847705075], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4372941299, 55845276163], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57858413599, 70072372275, 43514105207, 22072834423, 38682267135, 21502408191], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [55845279235], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57841704995, 57355245623, 39068146083, 13298352547, 55845282307], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61952125991, 40460658747, 51718090203, 34538299867, 8701396459], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [66112944171, 23364679747, 51835599295, 30360776127], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [66045838383, 10463003719, 51885934003, 21821176243], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65961955379, 47658078627, 13298352547], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [53312003127, 43111456223, 4456761823], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((36 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 36 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group36
end Z6969Source2391

-- Source: ProximityPrize.SubmissionLower.Low6969Mass37
section Z6969Source2392
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group37

private def m0 : MassCell 37 :=
  ⟨⟨1,3,74⟩,mass_cell 37 1 3 74 223 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1138422911309, 751365998725, 463315354117, 260013963725, 126974816989, 49480906549, 12585228245, 1110781117, 228157, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 37 :=
  ⟨⟨1,6,88⟩,mass_cell 37 1 6 88 204 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 832729561452, 459275749019, 215863316999, 78385440531, 17039720639, 923755425, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 37 :=
  ⟨⟨1,9,94⟩,mass_cell 37 1 9 94 190 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 878966293069, 476193405021, 188602354277, 49085644925, 4546088421, 1666560, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 37 :=
  ⟨⟨1,12,98⟩,mass_cell 37 1 12 98 179 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 516327628054, 175154884358, 32170134262, 953222221, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 37 :=
  ⟨⟨1,15,100⟩,mass_cell 37 1 15 100 170 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 537165286970, 157425650489, 18975180633, 71036904, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 37 :=
  ⟨⟨1,18,102⟩,mass_cell 37 1 18 102 164 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 564885207031, 151339797595, 12233170655, 239681, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 37 :=
  ⟨⟨1,21,103⟩,mass_cell 37 1 21 103 158 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 575354743676, 138552636335, 6878731949, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 37 :=
  ⟨⟨7,23,104⟩,mass_cell 37 7 23 104 156 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 589300486671, 136920414343, 5147310832, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 37 :=
  ⟨⟨7,27,105⟩,mass_cell 37 7 27 105 151 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 601407530262, 127643481754, 2390140696, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 37 :=
  ⟨⟨1,33,106⟩,mass_cell 37 1 33 106 145 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 613257396907, 116156347151, 590796120, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 37 :=
  ⟨⟨1,41,107⟩,mass_cell 37 1 41 107 139 (by decide)
    (by decide +kernel) [4468671078718, 3721807051950, 3062166708510, 2484603354766, 1983913673982, 1554837726318, 1192058948830, 890204155470, 624785130991, 105328094388, 36046966, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 37) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10]

end Low6969Allocation.Group37
end Z6969Source2392
