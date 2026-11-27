import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0847

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles25
section Z6969Source2369
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group25
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23625075719, 40588813327, 86978612255, 52887724091, 39616728355, 35170907427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34969655587, 21732572543, 17471084983, 13109013943, 8747007423, 1099819698623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819699647, 1099819700671, 43123221983, 25909949927, 17320088039, 140295655], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651924455, 1099651925479, 8679894511, 4351375855, 8629560831, 39631359], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301042183], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32199612427, 48944396311, 86962038823, 22974020675, 35204458791, 30741794087], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34818731303, 13176122775, 8780561835, 8713456043, 43324553647, 34701206959], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17437527499, 8847598027, 1099769366987, 1099769368011, 1099769369035, 1099702255067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702256091, 1099702257115, 4468813279, 4401706463, 17269754355, 56407547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099568036347, 30087472643, 21497611779], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40572036111, 69916183583, 69832642611, 39499353407, 26597750079, 26362941759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26195242303, 9116109119, 8864378279, 8780560807, 1099920360871, 1099819698623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819699647, 1099819700671, 13125784015, 8814043599, 1099719031255, 1099719032279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719033303, 43139999195, 4401704427, 1099635144171, 25775797767, 4300972551], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4301040135, 6074887], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40656252947, 74110556195, 52719951931, 35288275243, 30792121643, 30574091563], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21732506967, 8780561815, 1099987470743, 1099987471767, 1099987472791, 13192895911], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8830823847, 4535925159, 1099786142151, 1099786143175, 21665381851, 13058676187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4401704419, 1099668698595, 1099668699619, 1099668700643, 43039404531, 4384859635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [39628287, 39629311, 8595936775, 4300972551], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44800490519, 82566408231, 27117992003, 31094040847, 30792124687, 30590871823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100054579591, 1100054580615, 1100054581639, 13159344527, 8830892431, 1100021024143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17487858111, 8881151423, 1099769362891, 1099769363915, 1099769364939, 43173625299], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4468746707, 4401705427, 1099618365935, 1099618366959, 4317817343, 30070696455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4300971527, 4301039111, 6073863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48911042587, 86777559083, 5777378375, 30976604415, 34936101119, 22034496767], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8814116231, 1100054579591, 13343889803, 8965040523, 8830825867, 39046433195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26161607083, 1099903585707, 1099903586731, 1099819696575, 1099819697599, 1099786139079], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099786140103, 1099786141127, 17336864219, 4368083431, 1099651920359, 4351304187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56404475, 56405499, 12907679235, 4317748739], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57232675871, 73943059507, 30725016851, 26279128339, 9149597971, 39281317231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22118301039, 8897932687, 8797337999, 1100021024143, 1099970693531, 1099970694555], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099970695579, 13226448307, 8830821811, 1099802917315, 1099802918339, 1099802919363], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702251995, 1099702253019, 4384859631, 106737135, 38660625927, 8595936775], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4300972551, 6072839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61393494051, 56897477687, 22034488631, 21833168183, 4770811191, 35120570707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22168634707, 8814048655, 1100021023119, 1100021024143, 1100021025167, 1099903585707], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099903586731, 8897928639, 4552632767, 4485591487, 1099786140103, 1099786141127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099618365935, 1099618366959, 17236198907, 8646269435, 4317817343, 6072839], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6073863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74026806311, 31295452223, 31060487451, 26497158427, 22051268891, 13109084519], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100188799335, 1099953914271, 1099953915295, 1099953916319, 1099953917343, 8847600039], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4535924135, 1099920358823, 17437527499, 8797266379, 1099668698595, 1099668699619], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4368149991, 56405499, 1099568034299, 4334526975, 4317817343, 6072839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65520826411, 27034105923, 26648082739, 22135084339, 21900274995, 8797341043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100138467699, 8847601051, 4552702363, 1099970691483, 1099920360871, 1099920361895], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920362919, 13109007827, 4519077331, 4435258843, 1099702253019, 1099702254043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702255067, 39628287, 39629311, 25775798791], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65470563375, 14249870407, 26564265259, 26279125291, 17588534571, 8763784591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100021025167, 1100021026191, 1100021027215, 8981815719, 8814046631, 4502370727], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099836473787, 1099836474811, 1099702254043, 1099702255067, 4418481631, 1099685475807], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21598275051, 8713379307, 39628287, 39629311, 4301040135], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65403457587, 1465634891, 26480382239, 22000938271, 13343900959, 1100021024143], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100021025167, 1100021026191, 8864378271, 4552702367, 1099953914271, 1099903586731], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17420751307, 8780490187, 1099685476831, 1099685477855, 157069795, 1099668698595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4351305211, 56405499, 12890903047, 8595939847], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56863923255, 22118374703, 17655641391, 9049000239, 1099953916319, 1099953917343], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099953918367, 4552635811, 1099937136035, 1099937137059, 1099937138083, 13092232651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4502302155, 1099668698595, 1099668699619, 8629493247, 4334594559, 39629311], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((25 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 25 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group25
end Z6969Source2369

-- Source: ProximityPrize.SubmissionLower.Low6969Mass26
section Z6969Source2370
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group26

private def m0 : MassCell 26 :=
  ⟨⟨1,3,54⟩,mass_cell 26 1 3 54 236 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 1987956221280, 1464172661613, 1043305345245, 719728309533, 477323539437, 301409091597, 178739094333, 97503747645, 47329323213, 19278164397, 5848686237, 975375453, 29153872, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 26 :=
  ⟨⟨1,6,73⟩,mass_cell 26 1 6 73 209 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1156019482508, 730947528716, 432882780044, 234640340492, 112045185932, 43932164108, 12145994636, 1541269004, 12451606, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 26 :=
  ⟨⟨3,9,82⟩,mass_cell 26 3 9 82 191 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1254449006433, 782920073551, 413313323143, 189691636135, 69617492527, 16881948319, 1504635511, 890483, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 26 :=
  ⟨⟨1,12,86⟩,mass_cell 26 1 12 86 176 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 835888759071, 402045698499, 157499936007, 42512569323, 4842501999, 18027437, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 26 :=
  ⟨⟨4,14,89⟩,mass_cell 26 4 14 89 170 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 887001227426, 405579728044, 141297330396, 30310173708, 1827627580, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 26 :=
  ⟨⟨4,18,92⟩,mass_cell 26 4 18 92 159 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 932224023005, 406112123910, 112536244470, 13745743590, 78684528, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 26 :=
  ⟨⟨1,21,93⟩,mass_cell 26 1 21 93 153 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 944644955528, 397252311324, 91380158952, 6282581172, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 26 :=
  ⟨⟨3,22,94⟩,mass_cell 26 3 22 94 151 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 958323989365, 410721961068, 90056819564, 5445087596, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 26 :=
  ⟨⟨8,24,95⟩,mass_cell 26 8 24 95 149 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 968894479914, 413021808930, 78726734634, 3189770630, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 26 :=
  ⟨⟨8,27,96⟩,mass_cell 26 8 27 96 145 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 977498728446, 420358588844, 66762681944, 1344294640, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 26 :=
  ⟨⟨7,31,97⟩,mass_cell 26 7 31 97 140 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 429815103614, 53315916322, 305905607, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 26 :=
  ⟨⟨8,36,98⟩,mass_cell 26 8 36 98 136 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 442824450176, 39838836368, 14599562, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 26 :=
  ⟨⟨6,43,99⟩,mass_cell 26 6 43 99 131 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 455762969796, 26995272415, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 26 :=
  ⟨⟨33,33,98⟩,mass_cell 26 33 33 98 139 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 439189641277, 43375797349, 132772439, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 26 :=
  ⟨⟨23,41,99⟩,mass_cell 26 23 41 99 133 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 454338590289, 29050284321, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 26 :=
  ⟨⟨37,49,100⟩,mass_cell 26 37 49 100 129 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 465113514221, 18134659917, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 26 :=
  ⟨⟨60,19,96⟩,mass_cell 26 60 19 96 161 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 977210537666, 413621086678, 70852243178, 2862814809, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 26 :=
  ⟨⟨60,29,98⟩,mass_cell 26 60 29 98 144 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 436432670250, 45754142150, 450627206, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 26 :=
  ⟨⟨54,37,99⟩,mass_cell 26 54 37 99 136 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 451220423263, 31971580732, 12373041, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 26 :=
  ⟨⟨60,46,100⟩,mass_cell 26 60 46 100 130 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 463709153228, 19654597030, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 26 :=
  ⟨⟨46,26,97⟩,mass_cell 26 46 26 97 147 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 422289197438, 58210977966, 1375180162, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 26 :=
  ⟨⟨61,36,99⟩,mass_cell 26 61 36 99 137 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 450504395944, 32356090737, 24265971, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 26 :=
  ⟨⟨71,27,98⟩,mass_cell 26 71 27 98 147 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 436127202791, 45600978383, 440596203, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 26 :=
  ⟨⟨67,35,99⟩,mass_cell 26 67 35 99 138 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 450360349836, 32816173290, 39729345, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 26 :=
  ⟨⟨67,45,100⟩,mass_cell 26 67 45 100 131 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 463341059516, 20064920348, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 26 :=
  ⟨⟨71,21,97⟩,mass_cell 26 71 21 97 157 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 423855048318, 57896982834, 821783272, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 26 :=
  ⟨⟨79,33,99⟩,mass_cell 26 79 33 99 140 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 449595609983, 32843360669, 57823969, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 26 :=
  ⟨⟨93,14,97⟩,mass_cell 26 93 14 97 178 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 435505051972, 46646786728, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 26 :=
  ⟨⟨84,24,98⟩,mass_cell 26 84 24 98 152 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 437953528846, 44043671567, 45734077, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 26 :=
  ⟨⟨87,42,100⟩,mass_cell 26 87 42 100 133 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 462064913332, 20680479172, 284, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 26 :=
  ⟨⟨92,41,100⟩,mass_cell 26 92 41 100 134 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 462366778599, 20954892945, 75030, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 26 :=
  ⟨⟨98,40,100⟩,mass_cell 26 98 40 100 134 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 461983254392, 20800664894, 64596, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 26 :=
  ⟨⟨103,39,100⟩,mass_cell 26 103 39 100 135 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 462092154722, 20714829369, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 26 :=
  ⟨⟨89,31,99⟩,mass_cell 26 89 31 99 142 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 449817425247, 32384791329, 15392086, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 26 :=
  ⟨⟨111,15,98⟩,mass_cell 26 111 15 98 175 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 449870828212, 31457544553, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 26 :=
  ⟨⟨97,29,99⟩,mass_cell 26 97 29 99 145 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 451210770268, 31612095217, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 26 :=
  ⟨⟨105,9,97⟩,mass_cell 26 105 9 97 206 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 445058319691, 35778692035, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 26 :=
  ⟨⟨118,12,98⟩,mass_cell 26 118 12 98 188 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 454337581542, 26685445781, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 26 :=
  ⟨⟨108,26,99⟩,mass_cell 26 108 26 99 149 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 453374038419, 29035716160, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 26 :=
  ⟨⟨116,36,100⟩,mass_cell 26 116 36 100 138 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 463133483164, 19942443223, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 26 :=
  ⟨⟨117,23,99⟩,mass_cell 26 117 23 99 154 (by decide)
    (by decide +kernel) [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 456523849676, 26172700570, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 26) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40]

end Low6969Allocation.Group26
end Z6969Source2370

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles26
section Z6969Source2371
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group26
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23592307719, 40539137039, 86928804895, 52804362299, 39566986519, 35121165591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39181326615, 17454907755, 13277305239, 13159934359, 8831416727, 1099853776303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099853777327, 1099853778351, 1099853779375, 25977648591, 13092753871, 43140589011], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099702778323, 1099702779347, 1099702780371, 4435782107, 157594075, 1099669222875], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34416513523, 4335116791, 6597119, 6598143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 127 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 127 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 127 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32166713355, 53038626839, 86929075239, 18629247043, 30926859551, 34919910687], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30507512095, 39197948287, 30608089471, 13126381963, 1099920884127, 1099920885151], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920886175, 1099920887199, 1099920888223, 17488383399, 8915296679, 8814636455], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099753109959, 1099753110983, 140815839, 1099652444639, 1099652445663, 17253499375], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8646858227, 4335116791, 40151543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 127 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 127 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 127 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40539137039, 86828141599, 52703699003, 39634095359, 30960415999, 39214879999], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21733096787, 13327635847, 13210264967, 8848192903, 1099971215763, 1099971216787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971217811, 1099971218835, 1099971219859, 1099753108935, 1099753109959, 1099753110983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43140589011, 21649126871, 13059198423, 4452558295, 1099685998039, 1099685999063], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34450067947, 4351892979, 6596095, 6597119], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 127 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 127 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 127 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40606511123, 82566862883, 44147320891, 35322353931, 35037281547, 30608171275], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17404576091, 13193486735, 8831414671, 1099987991951, 1099971215763, 1099971216787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971217811, 1099971218835, 1099971219859, 21800123823, 13143086511, 1099736330699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099736331723, 1099736332747, 4419003867, 1099669220827, 43056771559, 8663635439], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4368671215, 30121614835, 23374331, 17186389503, 12891492863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 127 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 127 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 127 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44717128727, 78288742439, 31329596479, 30977124627, 30691985683, 30507510035], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100122212719, 1100122213743, 1100122214767, 13176711551, 8814639487, 1100055102847], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17488382379, 8915295659, 1099820218807, 1099820219831, 1099820220855, 43224546751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4452559303, 1099753107911, 1099753108935, 25843427823, 17253500399, 73705967], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099585334767, 8630082039, 23373307], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 127 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 127 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 127 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 127 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 127 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53038827547, 82499959855, 5710793799, 30859754759, 26397089031, 26229389575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8848193911, 1100088657271, 1100088658295, 39181175171, 26296349059, 1099937664411], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099937665435, 8965627295, 8831412639, 4502893983, 1099820219831, 1099820220855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13126307271, 1099702777299, 1099702778323, 157592027, 1099669220827, 1099669221851], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4318338555, 23373307], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 127 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 127 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 127 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 127 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 127 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61393949727, 69682237491, 26413863195, 26195766555, 9099856155, 35104314703], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26430568783, 8898522499, 8797862275, 1100038325635, 1099954440599, 1099954441623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099954442647, 13126309303, 4586775991, 1099820218807, 1099820219831, 1099820220855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099719552463, 1099719553487, 1099719554511, 21548464623, 12958601711, 4351894003], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6597119], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 127 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 127 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 127 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 127 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61377306659, 56864447543, 22018235695, 21850535215, 4754558255, 35053986127], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22152447311, 8797861259, 1100004770187, 1100004771211, 1100004772235, 1099920887199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099920888223, 8898518451, 4553222579, 4469338547, 1099786664383, 1099786665407], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652444639, 1099652445663, 17236723187, 8646859251, 56928755, 1099568557555], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34399805943, 6596095], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 127 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 127 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 127 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 127 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65554902055, 39802088511, 30893305143, 22169226551, 21917574455, 13176716627], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100239654227, 1100239655251, 1099937660315, 1099937661339, 1099937662363, 1099937663387], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8881743267, 4536447395, 1099904104867, 13025643999, 8730746335, 1099652444639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099652445663, 90483179, 90484203, 30071287295], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69732431915, 22756441155, 26699004191, 26397087007, 21917577503, 1100088658295], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088659319, 1100088660343, 8848191883, 1100004769163, 1100004770187, 1100004771211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13176640951, 8814634423, 1099736330699, 1099736331723, 1099736332747, 4368672239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [73706991, 25776323071, 12891493887], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82432853039, 30910088439, 30641726711, 13512262903, 13243819395, 8848192899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100038324611, 1099987993999, 1099987995023, 1099987996047, 1099987997071, 21733017027], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8848186819, 1099769886147, 1099769887171, 1099769888195, 4435782107, 1099669221851], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [6597119, 6598143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69648683059, 26514526483, 26246098195, 9133410579, 8948854151, 8814639495], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100021548423, 1099954440599, 1099954441623, 1099954442647, 1099786664383, 1099786665407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099786666431, 17387721159, 8781080007, 140816863, 1099652445663, 4335117815], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [40152567, 17203237371], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56864447543, 22085344559, 17656231215, 9032747311, 1099937663387, 1099937664411], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099937665435, 4553225635, 1099904105891, 1099904106915, 1099904107939, 13109599683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4519669187, 1099635668451, 1099635669475, 8613305851, 4318341627, 23376379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 127 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 127 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤127) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((26 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 26 where
  orders := orders
  covers := by
    intro a ha box
    change 15+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group26
end Z6969Source2371

-- Source: ProximityPrize.SubmissionLower.Low6969Mass27
section Z6969Source2372
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group27

private def m0 : MassCell 27 :=
  ⟨⟨1,3,72⟩,mass_cell 27 1 3 72 254 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1521594316284, 1118270026479, 769857618999, 509908152351, 322028154471, 191502089679, 105292358679, 52039298559, 22061182791, 7354221231, 1592560119, 128282079, 125733, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 27 :=
  ⟨⟨2,6,89⟩,mass_cell 27 2 6 89 225 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 861036782072, 523543643918, 292237075502, 146920722254, 63430757486, 21473189774, 4623862958, 328456142, 17185, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 27 :=
  ⟨⟨3,9,97⟩,mass_cell 27 3 9 97 206 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 572754240935, 285922840895, 121615788455, 39815843615, 7854086375, 409916735, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 27 :=
  ⟨⟨1,10,98⟩,mass_cell 27 1 10 98 200 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 583191667704, 284306433112, 115606016184, 34414586136, 5304069496, 107259766, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 27 :=
  ⟨⟨2,12,101⟩,mass_cell 27 2 12 101 191 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 614114160884, 284609188992, 103001120400, 24418888032, 2068390128, 728658, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 27 :=
  ⟨⟨4,15,104⟩,mass_cell 27 4 15 104 181 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 641784812166, 285380667787, 85933647427, 13618957315, 308037122, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 27 :=
  ⟨⟨5,18,106⟩,mass_cell 27 5 18 106 173 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 657709385112, 288907813200, 72526658448, 7167823824, 11751654, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 27 :=
  ⟨⟨4,20,107⟩,mass_cell 27 4 20 107 169 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 664355304591, 293615677232, 65899659784, 4595664736, 1392, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 27 :=
  ⟨⟨7,22,108⟩,mass_cell 27 7 22 108 165 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 669380615148, 297622942252, 58322519052, 2752400468, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 27 :=
  ⟨⟨1,26,109⟩,mass_cell 27 1 26 109 159 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 304062662236, 47608007932, 843097082, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 27 :=
  ⟨⟨1,30,110⟩,mass_cell 27 1 30 110 154 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 312336063264, 37866577440, 173554528, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 27 :=
  ⟨⟨10,33,111⟩,mass_cell 27 10 33 111 152 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 323326971365, 32313969865, 44920084, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 27 :=
  ⟨⟨13,39,112⟩,mass_cell 27 13 39 112 147 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 332304096118, 23633482200, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 27 :=
  ⟨⟨1,50,113⟩,mass_cell 27 1 50 113 141 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 340673767638, 14001276364, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 27 :=
  ⟨⟨56,15,109⟩,mass_cell 27 56 15 109 186 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 303604761821, 50542306574, 714668369, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 27 :=
  ⟨⟨57,25,111⟩,mass_cell 27 57 25 111 163 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 319977705780, 35384772829, 391987509, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 27 :=
  ⟨⟨52,33,112⟩,mass_cell 27 52 33 112 153 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 329537597644, 26392988227, 45169073, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 27 :=
  ⟨⟨13,48,113⟩,mass_cell 27 13 48 113 142 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 341080802378, 15308142088, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 27 :=
  ⟨⟨58,19,110⟩,mass_cell 27 58 19 110 175 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 311903557809, 43530871009, 568154978, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 27 :=
  ⟨⟨21,47,113⟩,mass_cell 27 21 47 113 143 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 340523588884, 15716014330, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 27 :=
  ⟨⟨62,31,112⟩,mass_cell 27 62 31 112 155 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 329330367432, 26640962969, 68430140, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 27 :=
  ⟨⟨61,41,113⟩,mass_cell 27 61 41 113 147 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 338317516914, 17567780263, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 27 :=
  ⟨⟨61,24,111⟩,mass_cell 27 61 24 111 165 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 320269663433, 35191001107, 288111179, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 27 :=
  ⟨⟨71,21,111⟩,mass_cell 27 71 21 111 171 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 322107914998, 33777172151, 8829766, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 27 :=
  ⟨⟨71,39,113⟩,mass_cell 27 71 39 113 148 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 338276437104, 17972648184, 331062, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 27 :=
  ⟨⟨81,52,114⟩,mass_cell 27 81 52 114 141 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346232172946, 9911886241, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 27 :=
  ⟨⟨86,51,114⟩,mass_cell 27 86 51 114 141 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346241486642, 10052028685, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 27 :=
  ⟨⟨76,38,113⟩,mass_cell 27 76 38 113 149 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 338164898808, 17988129328, 695723, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 27 :=
  ⟨⟨96,33,113⟩,mass_cell 27 96 33 113 154 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 338878267772, 17149604545, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 27 :=
  ⟨⟨96,49,114⟩,mass_cell 27 96 49 114 143 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346148272754, 10174741386, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 27 :=
  ⟨⟨102,18,112⟩,mass_cell 27 102 18 112 179 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 335902813259, 19848854971, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 27 :=
  ⟨⟨101,48,114⟩,mass_cell 27 101 48 114 143 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346043305654, 10139027909, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 27 :=
  ⟨⟨105,47,114⟩,mass_cell 27 105 47 114 144 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346191048985, 10165965883, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 27 :=
  ⟨⟨108,29,113⟩,mass_cell 27 108 29 113 159 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 340426638700, 15615865862, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 27 :=
  ⟨⟨109,46,114⟩,mass_cell 27 109 46 114 144 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346307932906, 10126852345, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 27 :=
  ⟨⟨108,15,112⟩,mass_cell 27 108 15 112 189 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 338316733271, 17651972130, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 27 :=
  ⟨⟨113,45,114⟩,mass_cell 27 113 45 114 145 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346392934992, 10017685922, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 27 :=
  ⟨⟨96,10,111⟩,mass_cell 27 96 10 111 213 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 333070920826, 23009604191, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 27 :=
  ⟨⟨103,6,111⟩,mass_cell 27 103 6 111 247 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 337161278426, 18758194474, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 27 :=
  ⟨⟨108,3,111⟩,mass_cell 27 108 3 111 293 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 339824150586, 15591028242, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 27 :=
  ⟨⟨117,44,114⟩,mass_cell 27 117 44 114 146 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346445019817, 9836112250, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 27 :=
  ⟨⟨114,12,112⟩,mass_cell 27 114 12 112 202 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 340300309652, 15126169728, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 27 :=
  ⟨⟨121,43,114⟩,mass_cell 27 121 43 114 146 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346463140015, 9585974994, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 27 :=
  ⟨⟨118,25,113⟩,mass_cell 27 118 25 113 165 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 342354586240, 13723537254, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 27 :=
  ⟨⟨124,42,114⟩,mass_cell 27 124 42 114 147 (by decide)
    (by decide +kernel) [4443300502124, 3665941319948, 2995100127212, 2420593723148, 1932749510252, 1522405494284, 1180910284268, 900123092492, 672413734508, 346767813564, 9456515211, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 27) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44]

end Low6969Allocation.Group27
end Z6969Source2372

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles27
section Z6969Source2373
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group27
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27687128071, 40489854995, 86913011743, 48493536315, 35289714963, 35038131475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39115069715, 17388650855, 13278222723, 17388644739, 13043350915, 1099905027483], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099905028507, 1099837914539, 1099837915563, 1099837916587, 1099837917611, 21750707639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13160779191, 4486965687, 1099787514295, 1099787515319, 1099787581879, 38846540235], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34518011347, 4386299363, 91334115, 74557927, 1099586252263, 34383876595], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 125 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 125 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 125 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36244625419, 82567511063, 74061941811, 39685274879, 31045149951, 43493917951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30407766319, 1100357947695, 17657070979, 13261445507, 8916150659, 13060126083], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8748451203, 1099837916587, 1099837917611, 1099837918635, 1099821069743, 1099821070767], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099821137327, 1099821138351, 38829758927, 1099670071763, 1099670072787, 1099670073811], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8664488415, 108111327, 25827567083, 17237639659, 4319189491, 24224243], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [38662062583, 8597378551], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 125 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 125 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 125 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40540120079, 82567646239, 56966028343, 39567904007, 35071685895, 30642575623], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21750724935, 1100257349959, 8748382603, 1099972134283, 1099972135307, 1099972136331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13194336659, 8832264595, 8748381587, 21767484851, 13177556403, 1099804361139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770738107, 1099770804667, 1099770805691, 1099686848975, 1099686849999, 1099686851023], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [43107952083, 4403076575, 108111327, 34450985443], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 125 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 125 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 125 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40607494163, 82567780387, 44148238395, 35289717003, 30810340619, 30592245003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13160791387, 1100173462875, 1100173463899, 13194337675, 8832265611, 8748382603], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888248223, 1099888249247, 1099804293555, 1099804360115, 1099804361139, 21700378047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8832259519, 1099720404423, 1099720405447, 1099720472007, 4419854807, 141666775], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [43024134631, 30122466795, 17187306999, 8597377527, 7447031, 7448055], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44734888983, 78306437159, 31313671231, 30944487703, 30676125975, 26263791895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8798717291, 1100106355051, 8865819023, 8765158799, 1099955290511, 1099888248223], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888249247, 1099888250271, 17472522667, 8865815979, 1099770738107, 1099770804667], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770805691, 43175132611, 158443987, 1099670072787, 1099670073811, 30122535403], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4335967727, 41002479, 12909119987, 8614156787], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48878995483, 86779000875, 5728488519, 30910937343, 39131846911, 17740972287], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13362108787, 13211117939, 8849045875, 1099988911495, 1099988912519, 1099888250271], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888251295, 39014386083, 26129494435, 1099804293555, 1099804360115, 1099804361139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4453411267, 1099737182659, 1099737183683, 13076893131, 4369522151, 4352746983], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57847275, 7448055, 7514615], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [69850584095, 61160265783, 39467308335, 26532150575, 22035863855, 21884940591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9016822063, 8798712211, 1099938512275, 1099938513299, 1099938579859, 1099921803671], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099921804695, 1099921805719, 13093673399, 4520520119, 1099720405447, 1099720472007], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099720473031, 21549383143, 12942677479, 4352746987, 41070063, 38678844915], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8597378551, 4302414327], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [78306369571, 39836494911, 35323339027, 30776788243, 30541980947, 13093684571], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13194339719, 8815490439, 1099988844935, 1099955357071, 1099955358095, 1099955359119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099955360143, 21700380095, 8832261567, 1099753960895, 1099754027455, 1099754028479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4419856851, 1099670073811, 4319259123, 17187309047, 8597379575], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69817166887, 35575083071, 30910934319, 26397936943, 26179905839, 8849048931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100139909475, 8916150675, 8781936019, 1099938513299, 1099871471011, 1099871472035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099871473059, 1099737183683, 1099737250243, 1099737251267, 17388637639, 8781930951], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [91336163, 91402723, 4302414327, 4302481911], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [82517588011, 10006677575, 30978046215, 34903988487, 21985606919, 8798715267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13345331595, 8966482315, 8832267659, 1099905026459, 1099905027483, 1099905028507], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099787583927, 1099787584951, 4403148231, 1099720474055, 25861126627, 12976231907], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [91403747, 1099603032547, 4369525223, 74625511], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78239466543, 1483853899, 30860674319, 26381231375, 17707417871, 1099955290511], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099955357071, 1099955358095, 1099955359119, 8932926883, 8798712227, 1099871403427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099821142447, 21650048463, 13043342799, 4403147223, 1099653364183, 24293875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [24294899, 8597380599, 4302481911], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69699866675, 26498601247, 22035934495, 13378897183, 1099921802647, 1099921803671], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099921804695, 1099921805719, 8849042855, 4503746983, 1099854692775, 17355084239], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8765154767, 1099636586971, 1099636587995, 4352815591, 7516663, 7517687], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56932473911, 26280566079, 21817833791, 1100290838847, 8815491475, 4503815571], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099938581907, 13144006075, 8781934011, 1099720476103, 1099720477127, 4403149259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099703697867, 74627559, 1099586256359, 4352814571, 57849323], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((27 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 27 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group27
end Z6969Source2373

-- Source: ProximityPrize.SubmissionLower.Low6969Mass28
section Z6969Source2374
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group28

private def m0 : MassCell 28 :=
  ⟨⟨1,3,120⟩,mass_cell 28 1 3 120 302 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421510258546, 268376784933, 152371018821, 78682772181, 35533317909, 13063729989, 3334883493, 339408062, 53725, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 28 :=
  ⟨⟨2,6,132⟩,mass_cell 28 2 6 132 268 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287523079756, 161183334832, 71758798432, 26078125840, 6772096960, 914635888, 22810854, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 28 :=
  ⟨⟨2,9,137⟩,mass_cell 28 2 9 137 246 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 172996832514, 69250875352, 20376342196, 3471013240, 148536484, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 28 :=
  ⟨⟨1,12,140⟩,mass_cell 28 1 12 140 230 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 180059512182, 69074434107, 16503732207, 1630966851, 5158377, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 28 :=
  ⟨⟨1,15,142⟩,mass_cell 28 1 15 142 219 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 183968630220, 68678864976, 12889848468, 605467655, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 28 :=
  ⟨⟨3,18,144⟩,mass_cell 28 3 18 144 211 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 186961812912, 70894133292, 10376459148, 206565096, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 28 :=
  ⟨⟨2,21,145⟩,mass_cell 28 2 21 145 205 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 72051553257, 8309602257, 47010741, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 28 :=
  ⟨⟨8,23,146⟩,mass_cell 28 8 23 146 201 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 73848423714, 6844753622, 14112215, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 28 :=
  ⟨⟨1,29,147⟩,mass_cell 28 1 29 147 193 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 76110398008, 4654368580, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 28 :=
  ⟨⟨7,34,148⟩,mass_cell 28 7 34 148 188 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 77657149303, 3163887213, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 28 :=
  ⟨⟨13,42,149⟩,mass_cell 28 13 42 149 182 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 79090331574, 1759615200, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 28 :=
  ⟨⟨72,18,149⟩,mass_cell 28 72 18 149 216 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 79880035991, 966782247, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 28 :=
  ⟨⟨85,33,150⟩,mass_cell 28 85 33 150 191 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 80335388708, 512040501, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 28 :=
  ⟨⟨94,27,150⟩,mass_cell 28 94 27 150 199 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 80449316640, 254762156, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 28 :=
  ⟨⟨97,24,150⟩,mass_cell 28 97 24 150 204 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 80641886112, 184731741, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 28 :=
  ⟨⟨112,9,150⟩,mass_cell 28 112 9 150 259 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 80823987424, 14043885, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 28 :=
  ⟨⟨115,6,150⟩,mass_cell 28 115 6 150 286 (by decide)
    (by decide +kernel) [4425428026074, 3620992865538, 2930715782058, 2343325556946, 1848133238394, 1435032141474, 1094497848138, 817588207218, 595943334426, 421785612354, 287919690474, 187732485138, 80742805820, 6438740, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 28) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16]

end Low6969Allocation.Group28
end Z6969Source2374

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles28
section Z6969Source2375
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group28
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [36414426119, 57773142035, 87301449767, 23279811651, 56347683191, 43462861175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60189716963], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 123 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 123 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 123 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [49199454219, 87284533275, 57505258551, 60709751143, 52119897447, 25947453895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51616553439], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 123 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 123 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 123 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [57722610703, 87335001123, 36181487679, 60625870203, 47741049211, 60256822739], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i9 : checks (tilesOf batches) 123 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 123 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 123 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [62034554899, 87335005223, 18984845379, 60609162623, 43429308799, 64518238683], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 123 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 123 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 123 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [66296101911, 87318297647, 1771425867, 60575612291, 26232666499, 64535018967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [55844437487, 30074648047], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 123 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 123 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 123 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 123 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 123 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [66363344923, 78829094963, 56179984799, 17525293471, 68746103275], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 123 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 123 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 123 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 123 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 123 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [87402042399, 44788197435, 69165471111, 56263874951, 51549477359], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 123 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 123 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 123 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 123 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [87418888227, 31886521407, 69131985295, 47657166223], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 123 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 123 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 123 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 123 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [87418891303, 18984845379, 69115211155, 34755490195], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87418959915, 6083169351, 69081659799, 21853814167, 64434371055, 25779681775], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [83157550127, 64753141155, 13213549987], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [70457266227, 64551817683, 127324627], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [57689807927], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 123 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 123 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤123) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((28 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 28 where
  orders := orders
  covers := by
    intro a ha box
    change 19+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group28
end Z6969Source2375

-- Source: ProximityPrize.SubmissionLower.Low6969Mass29
section Z6969Source2376
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group29

private def m0 : MassCell 29 :=
  ⟨⟨1,3,34⟩,mass_cell 29 1 3 34 198 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3240995387441, 2554253280047, 1927222873963, 1411659219079, 996922155395, 672274754911, 426883321627, 249817391543, 130049732659, 56456344975, 17816460491, 2812543207, 47589622, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 29 :=
  ⟨⟨2,6,55⟩,mass_cell 29 2 6 55 180 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2192998827292, 1514539017291, 967797908851, 571036482939, 300696226083, 132869354539, 43298814291, 7378281051, 170601674, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 29 :=
  ⟨⟨3,9,64⟩,mass_cell 29 3 9 64 166 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1688536739727, 993540495540, 515719602164, 222437018420, 69168405108, 10483453364, 146960466, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 29 :=
  ⟨⟨3,10,66⟩,mass_cell 29 3 10 66 162 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1732814054055, 1009780924827, 503355608531, 202744594931, 55023318651, 5806992107, 8826932, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 29 :=
  ⟨⟨4,12,69⟩,mass_cell 29 4 12 69 154 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1788269985731, 1038939353757, 475818747605, 165239577941, 32580684189, 1283153246, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 29 :=
  ⟨⟨1,15,72⟩,mass_cell 29 1 15 72 146 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1825001225690, 1095123181599, 448468384355, 123852293639, 13357901835, 22154881, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 29 :=
  ⟨⟨1,17,73⟩,mass_cell 29 1 17 73 140 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1104926302632, 413565284712, 94169869608, 5714023656, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 29 :=
  ⟨⟨1,18,74⟩,mass_cell 29 1 18 74 139 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1143478229983, 414148337783, 87478764583, 4151391417, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 29 :=
  ⟨⟨1,21,76⟩,mass_cell 29 1 21 76 133 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1211707711261, 401347557478, 65364529078, 1156658595, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 29 :=
  ⟨⟨1,24,77⟩,mass_cell 29 1 24 77 129 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1235667647036, 370591662533, 43692853773, 131578363, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 29 :=
  ⟨⟨1,26,78⟩,mass_cell 29 1 26 78 127 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1272495064276, 369345855705, 36358310625, 21824418, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 29 :=
  ⟨⟨6,29,79⟩,mass_cell 29 6 29 79 123 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1302447544644, 351743160318, 25056228318, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 29 :=
  ⟨⟨10,33,80⟩,mass_cell 29 10 33 80 120 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1332727560951, 331697467388, 15009289951, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 29 :=
  ⟨⟨4,39,81⟩,mass_cell 29 4 39 81 115 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1363877877655, 309155935592, 6602079171, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 29 :=
  ⟨⟨14,46,82⟩,mass_cell 29 14 46 82 112 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1393238717067, 284373516727, 2149137659, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 29 :=
  ⟨⟨94,32,81⟩,mass_cell 29 94 32 81 122 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1357730085398, 308424356686, 12971948554, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 29 :=
  ⟨⟨42,44,82⟩,mass_cell 29 42 44 82 113 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1391923522585, 285368961679, 2998718873, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 29 :=
  ⟨⟨94,26,80⟩,mass_cell 29 94 26 80 129 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1325376047025, 330090490710, 24775042050, 41721550, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 29 :=
  ⟨⟨93,40,82⟩,mass_cell 29 93 40 82 116 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389787253636, 285200012825, 4820103241, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 29 :=
  ⟨⟨89,22,79⟩,mass_cell 29 89 22 79 134 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1292493699677, 347848864344, 37840888500, 439453634, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 29 :=
  ⟨⟨112,24,80⟩,mass_cell 29 112 24 80 132 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1324982505990, 329077094522, 24779750982, 47222359, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 29 :=
  ⟨⟨104,39,82⟩,mass_cell 29 104 39 82 116 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389473993118, 285244206584, 5246357470, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 29 :=
  ⟨⟨109,50,83⟩,mass_cell 29 109 50 83 110 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1420113174549, 259203907949, 947288847, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 29 :=
  ⟨⟨132,6,77⟩,mass_cell 29 132 6 77 202 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1254294644094, 399440338349, 25340798816, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 29 :=
  ⟨⟨126,12,78⟩,mass_cell 29 126 12 78 163 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1269439228156, 373336309739, 33722047617, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 29 :=
  ⟨⟨121,49,83⟩,mass_cell 29 121 49 83 111 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1419876275602, 258956334004, 1085791394, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 29 :=
  ⟨⟨105,20,79⟩,mass_cell 29 105 20 79 139 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1292887998465, 348457959624, 37386662196, 293032664, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 29 :=
  ⟨⟨132,48,83⟩,mass_cell 29 132 48 83 112 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1419712446800, 258957005156, 1224548982, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 29 :=
  ⟨⟨134,15,79⟩,mass_cell 29 134 15 79 153 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1299105611114, 355611082122, 25667747136, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 29 :=
  ⟨⟨133,21,80⟩,mass_cell 29 133 21 80 137 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1326457408416, 330644793962, 21202186188, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 29 :=
  ⟨⟨115,38,82⟩,mass_cell 29 115 38 82 117 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389142549684, 284806393320, 5590689616, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 29) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30]

end Low6969Allocation.Group29
end Z6969Source2376

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles29
section Z6969Source2377
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group29
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [28087290887, 57986394131, 87649247267, 27855533117, 69144175047, 43391296967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60235262487, 64429778479], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [45117544459, 62315381787, 83287310383, 56292901315, 21933242817, 55957068307], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [64463262247], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [53708071951, 79008913443, 45052175419, 60621281723, 47736526267, 60235261463], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [58003370003, 83169798183, 23543855171, 56443824543, 43559068063, 60218552859], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [58070678551, 78874899499, 14953922625, 52132083107, 39213771171, 34381933099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60134735407], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [58070812699, 82985320495, 48004956539, 30825165179], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [58037392415, 70251482163, 43542220195, 22067460515, 60134807087], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57953574947, 57484023863, 39096261059, 13343310275, 55906951711, 38660119087], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70385560615, 32049836095, 52048194999, 34868470199, 8679310873], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [66124216363, 23543855171, 47702899139, 30523173315], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [66040398895, 10642179141, 47736522163, 26278540723, 42971792939, 25792000555], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61728657459, 2052246597, 39180145075, 22000351667], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [53239454775, 39029218767, 8998012365, 34381930027, 12907168297], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [40522328123, 30288292347, 4518562297], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((29 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 29 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 7+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6969Allocation.Group29
end Z6969Source2377

-- Source: ProximityPrize.SubmissionLower.Low6969Mass30
section Z6969Source2378
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group30

private def m0 : MassCell 30 :=
  ⟨⟨1,3,34⟩,mass_cell 30 1 3 34 198 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3240995387441, 2554253280047, 1927222873963, 1411659219079, 996922155395, 672274754911, 426883321627, 249817391543, 130049732659, 56456344975, 17816460491, 2812543207, 47589622, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 30 :=
  ⟨⟨2,6,55⟩,mass_cell 30 2 6 55 180 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2192998827292, 1514539017291, 967797908851, 571036482939, 300696226083, 132869354539, 43298814291, 7378281051, 170601674, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 30 :=
  ⟨⟨3,9,64⟩,mass_cell 30 3 9 64 166 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1688536739727, 993540495540, 515719602164, 222437018420, 69168405108, 10483453364, 146960466, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 30 :=
  ⟨⟨4,12,69⟩,mass_cell 30 4 12 69 154 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1788269985731, 1038939353757, 475818747605, 165239577941, 32580684189, 1283153246, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 30 :=
  ⟨⟨1,14,71⟩,mass_cell 30 1 14 71 148 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1815858834450, 1073111246768, 456858613676, 136526166992, 18255502748, 129692294, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 30 :=
  ⟨⟨1,15,72⟩,mass_cell 30 1 15 72 146 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1825001225690, 1095123181599, 448468384355, 123852293639, 13357901835, 22154881, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 30 :=
  ⟨⟨1,18,74⟩,mass_cell 30 1 18 74 139 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1143478229983, 414148337783, 87478764583, 4151391417, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 30 :=
  ⟨⟨3,19,75⟩,mass_cell 30 3 19 75 137 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1180247690203, 414351294509, 81053582681, 2995378042, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 30 :=
  ⟨⟨1,21,76⟩,mass_cell 30 1 21 76 133 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1211707711261, 401347557478, 65364529078, 1156658595, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 30 :=
  ⟨⟨1,24,77⟩,mass_cell 30 1 24 77 129 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1235667647036, 370591662533, 43692853773, 131578363, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 30 :=
  ⟨⟨1,26,78⟩,mass_cell 30 1 26 78 127 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1272495064276, 369345855705, 36358310625, 21824418, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 30 :=
  ⟨⟨6,29,79⟩,mass_cell 30 6 29 79 123 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1302447544644, 351743160318, 25056228318, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 30 :=
  ⟨⟨10,33,80⟩,mass_cell 30 10 33 80 120 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1332727560951, 331697467388, 15009289951, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 30 :=
  ⟨⟨4,39,81⟩,mass_cell 30 4 39 81 115 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1363877877655, 309155935592, 6602079171, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 30 :=
  ⟨⟨1,47,82⟩,mass_cell 30 1 47 82 111 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1393712934209, 282712360911, 1759551593, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 30 :=
  ⟨⟨46,36,81⟩,mass_cell 30 46 36 81 118 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1360654909177, 309921768001, 9549600560, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 30 :=
  ⟨⟨14,46,82⟩,mass_cell 30 14 46 82 112 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1393238717067, 284373516727, 2149137659, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 30 :=
  ⟨⟨42,44,82⟩,mass_cell 30 42 44 82 113 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1391923522585, 285368961679, 2998718873, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 30 :=
  ⟨⟨69,24,79⟩,mass_cell 30 69 24 79 131 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1293953938381, 349563319729, 36217870697, 219096319, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 30 :=
  ⟨⟨55,19,77⟩,mass_cell 30 55 19 77 139 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1229357008894, 381826599173, 65202045121, 2604060785, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 30 :=
  ⟨⟨63,29,80⟩,mass_cell 30 63 29 80 124 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1327080834486, 330465019446, 21455417286, 423783, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 30 :=
  ⟨⟨69,42,82⟩,mass_cell 30 69 42 82 114 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1390667507557, 285194216389, 3905309035, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 30 :=
  ⟨⟨53,22,78⟩,mass_cell 30 53 22 78 133 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1262700861379, 366987916696, 48752989820, 721830433, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 30 :=
  ⟨⟨59,35,81⟩,mass_cell 30 59 35 81 119 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1359733885241, 309663766279, 10513563501, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 30 :=
  ⟨⟨83,19,78⟩,mass_cell 30 83 19 78 140 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1259806128656, 364614346943, 52267805667, 1559779070, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 30 :=
  ⟨⟨85,27,80⟩,mass_cell 30 85 27 80 127 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1325490024411, 329382764045, 23788010521, 18856245, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 30 :=
  ⟨⟨97,51,83⟩,mass_cell 30 97 51 83 110 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1420342703133, 259147387955, 805950611, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 30 :=
  ⟨⟨93,40,82⟩,mass_cell 30 93 40 82 116 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389787253636, 285200012825, 4820103241, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 30 :=
  ⟨⟨97,21,79⟩,mass_cell 30 97 21 79 136 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1292730467746, 348631429390, 38195872798, 462127111, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 30 :=
  ⟨⟨109,50,83⟩,mass_cell 30 109 50 83 110 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1420113174549, 259203907949, 947288847, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 30 :=
  ⟨⟨104,39,82⟩,mass_cell 30 104 39 82 116 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389473993118, 285244206584, 5246357470, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 30 :=
  ⟨⟨115,38,82⟩,mass_cell 30 115 38 82 117 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1389142549684, 284806393320, 5590689616, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 30 :=
  ⟨⟨118,18,79⟩,mass_cell 30 118 18 79 144 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1294711911431, 350871543282, 34171354468, 31465, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 30 :=
  ⟨⟨83,33,81⟩,mass_cell 30 83 33 81 121 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1358267429816, 308884870212, 12261183344, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 30 :=
  ⟨⟨125,37,82⟩,mass_cell 30 125 37 82 118 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1388951982076, 284699746456, 5883176188, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 30 :=
  ⟨⟨121,49,83⟩,mass_cell 30 121 49 83 111 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1419876275602, 258956334004, 1085791394, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 30 :=
  ⟨⟨121,9,77⟩,mass_cell 30 121 9 77 179 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1243026032200, 392777158064, 39974230596, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 30 :=
  ⟨⟨129,3,76⟩,mass_cell 30 129 3 76 240 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1234511681578, 414865670511, 23845729591, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 30 :=
  ⟨⟨126,12,78⟩,mass_cell 30 126 12 78 163 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1269439228156, 373336309739, 33722047617, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 30 :=
  ⟨⟨104,31,81⟩,mass_cell 30 104 31 81 123 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1357416234885, 308323166936, 13571033008, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 30 :=
  ⟨⟨134,15,79⟩,mass_cell 30 134 15 79 153 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1299105611114, 355611082122, 25667747136, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 30 :=
  ⟨⟨122,29,81⟩,mass_cell 30 122 29 81 125 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1357218337512, 308400404748, 14130741660, 427840, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 30 :=
  ⟨⟨134,36,82⟩,mass_cell 30 134 36 82 119 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1388905442723, 284991766441, 6114409157, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 30 :=
  ⟨⟨132,48,83⟩,mass_cell 30 132 48 83 112 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1419712446800, 258957005156, 1224548982, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 30 :=
  ⟨⟨119,23,80⟩,mass_cell 30 119 23 80 134 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1325514403713, 330308518749, 24430603353, 6720439, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 30 :=
  ⟨⟨130,28,81⟩,mass_cell 30 130 28 81 127 (by decide)
    (by decide +kernel) [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1357342898487, 308685160923, 13986946942, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 30) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45]

end Low6969Allocation.Group30
end Z6969Source2378

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles30
section Z6969Source2379
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group30
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23607774215, 40789615631, 87078685727, 48793493563, 39683181883, 35287758139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39280810299, 13209092527, 17571158483, 13209087443, 8847015379, 1099718445567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099718446591, 34532494855, 43089015311, 4367498771, 1099634558483, 30153995803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17269167643, 8645684771, 4333943331, 39043623, 5421615, 5422639], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32366860299, 40857188375, 87028490275, 27385771071, 35405127987, 30892131635], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34918737203, 13292971451, 8897344963, 8796684739, 1099970104771, 1099751932407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099751998967, 1099751999991, 21698283003, 13108420091, 4367496719, 1099651268111], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4367494687, 55752227, 1099567381027, 42988354087, 30070040111], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40722506767, 65771621407, 69882383411, 26479791435, 26278537547, 9182561611], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39481920867, 26613937507, 8930896327, 8796681671, 1099953258951, 1099869373915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099869440475, 1099869441499, 13125128695, 8813453815, 1099735152123, 1099735153147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099735154171, 43156055551, 89304603, 89305627, 34381713963, 25775142447], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4300382767, 4300384815], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40840278035, 69915662371, 52786469943, 35321174339, 26613939523, 22151272771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17621496163, 9014789475, 1099936482763, 1099936549323, 1099936550347, 4535267791], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099919702479, 1099919703503, 1099919704527, 8897337831, 4602373607, 4484935143], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099668043275, 21614394895, 13007754767, 106081815, 1099617710615, 43021906463], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30086815275, 8595346991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40806923287, 69848622119, 39951902779, 31093384503, 26530055479, 26278469943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13175537011, 1100305583475, 9014780339, 8863788467, 1100037142963, 1100003589563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003590587, 1100003591611, 1100003658171, 17453647343, 8863783407, 1099751927287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751928311, 1099751929335, 43038752283, 89302555, 89303579, 25775073839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44850366491, 65553789995, 27117335615, 26714600763, 22201602363, 17772489019], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8847015299, 1100238473603, 1100238474627, 1099970035139, 1099970036163, 1099970037187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4585597387, 1099936477643, 1099936478667, 1099936479691, 38978669027, 26077065699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13108351467, 4585595371, 1099634485779, 1099634486803, 12957355551, 4350713379], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25775141423], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48927364127, 69697831983, 5810341959, 26613941531, 22134497563, 21933242651], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8830237067, 1100204918155, 34885031347, 22000204211, 1100037147059, 1100037213619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8930894267, 4585598395, 1100003587515, 1099953256903, 1099953257927, 1099953258951], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13125128679, 1099701595651, 1099701596675, 4417823247, 1099651262991, 8645677603], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4350713379, 5416495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57198600227, 56829712437, 22151272743, 21933240615, 1100624349479, 1100624350503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30892056939, 22184755563, 8847012247, 1100154584471, 1100154585495, 1100154586519], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8947603915, 4635928011, 4501712331, 1099886147031, 1099886148055, 1099718372863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718373887, 17285874199, 8696010263, 72525343, 1099584154143, 4333937187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5415471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [48742951975, 52585143351, 17873083699, 17655050547, 9031566643, 30657244559], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17722084751, 1100121032095, 1100121033119, 1100121099679, 4585599399, 1100087474599], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100087475623, 1100087476647, 4635927003, 4501711323, 1099785482735, 1099785483759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651262991, 1099651264015, 13007687187, 4417822227, 25842183711, 12957354527], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5416495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52836661291, 35522718783, 13360082263, 13158759767, 1100423023959, 26530052451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17789195619, 13360081251, 1100137807259, 1100137808283, 1100137809307, 1100137810331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936479691, 4518488535, 1099886146007, 1099886147031, 8830227959, 4535263735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651262991, 1099651264015, 21564062235, 12974199323], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73892135981, 1498598471, 26748159235, 26395910403, 17705385219, 1100238470531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100238471555, 1100238472579, 1100238473603, 9081889179, 8880565659, 1100137806235], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100053990831, 1099835813347, 1099835814371, 1099835815395, 17453647343, 8863783407], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [122856979, 122858003], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65335758897, 22402928911, 22067390735, 13410418959, 1100188139919, 1100188140943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100188141967, 1100188208527, 8947673503, 1100121027999, 1100121029023, 1100121030047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13141905903, 4568818159, 240298487, 1099751927287, 1099751928311, 12890313263], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52568366133, 22100942127, 17621497135, 1100590795055, 1100590796079, 4602377627], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100137807259, 1100137808283, 1100137809307, 8998002119, 4619151815, 1099953254855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819038183, 1099819039207, 106080791, 1099617709591, 4317158955, 22193707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤51) :
    Covered orders a ∨ Low6969Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 30 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group30
end Z6969Source2379

-- Source: ProximityPrize.SubmissionLower.Low6969Mass31
section Z6969Source2380
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group31

private def m0 : MassCell 31 :=
  ⟨⟨1,3,44⟩,mass_cell 31 1 3 44 208 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2590812029748, 1968873697994, 1437125166362, 1013239001130, 683971810298, 436481097866, 258325263834, 137463604202, 62256310970, 21464472138, 4250071706, 176432971, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 31 :=
  ⟨⟨2,6,64⟩,mass_cell 31 2 6 64 189 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1629104551453, 1056813787471, 635593311519, 345922020087, 162147822295, 59362724799, 13402831791, 848344999, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 31 :=
  ⟨⟨1,9,72⟩,mass_cell 31 1 9 72 174 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1715936876996, 1145770716464, 623165123728, 290268958192, 104329564496, 22367794864, 1178135497, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 31 :=
  ⟨⟨3,12,77⟩,mass_cell 31 3 12 77 162 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1247405143383, 624728492483, 247016916747, 65074225739, 6406444163, 5404671, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 31 :=
  ⟨⟨3,15,80⟩,mass_cell 31 3 15 80 154 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1304076763398, 633269385638, 212945943430, 39059771686, 1194255589, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 31 :=
  ⟨⟨1,18,82⟩,mass_cell 31 1 18 82 147 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1335978255499, 645289768569, 184814665417, 22171864665, 82868358, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 31 :=
  ⟨⟨1,20,83⟩,mass_cell 31 1 20 83 143 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1348679889889, 650586971067, 166071215859, 14337916755, 1664004, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 31 :=
  ⟨⟨1,22,84⟩,mass_cell 31 1 22 84 139 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1358755929529, 664771644156, 152156471016, 9386087044, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 31 :=
  ⟨⟨7,24,85⟩,mass_cell 31 7 24 85 137 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 681062996264, 137902884316, 5967406391, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 31 :=
  ⟨⟨9,27,86⟩,mass_cell 31 9 27 86 133 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 702995749994, 119845344890, 2785695225, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 31 :=
  ⟨⟨1,32,87⟩,mass_cell 31 1 32 87 128 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 722830812722, 95091924916, 520526612, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 31 :=
  ⟨⟨12,36,88⟩,mass_cell 31 12 36 88 125 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 746450518937, 79918518848, 95613390, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 31 :=
  ⟨⟨1,44,89⟩,mass_cell 31 1 44 89 120 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 768043100665, 57590885721, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 31 :=
  ⟨⟨39,34,88⟩,mass_cell 31 39 34 88 127 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 742830739716, 83124422845, 281003101, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 31 :=
  ⟨⟨42,41,89⟩,mass_cell 31 42 41 89 122 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 764372117723, 61640150752, 1750140, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 31 :=
  ⟨⟨72,49,90⟩,mass_cell 31 72 49 90 118 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 783630095624, 42888934307, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 31 :=
  ⟨⟨23,30,87⟩,mass_cell 31 23 30 87 130 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 722407024351, 101914940267, 1161973416, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 31 :=
  ⟨⟨67,39,89⟩,mass_cell 31 67 39 89 123 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 762125751015, 63711730442, 20343668, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 31 :=
  ⟨⟨64,19,85⟩,mass_cell 31 64 19 85 147 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 668816534181, 145041528113, 12602597981, 40598191, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 31 :=
  ⟨⟨52,33,88⟩,mass_cell 31 52 33 88 128 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 740929140552, 84205623820, 416812372, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 31 :=
  ⟨⟨70,26,87⟩,mass_cell 31 70 26 87 136 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 715416580814, 106984889907, 2920502671, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 31 :=
  ⟨⟨58,23,86⟩,mass_cell 31 58 23 86 140 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 692944798931, 125786394935, 6190674299, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 31 :=
  ⟨⟨63,32,88⟩,mass_cell 31 63 32 88 129 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 740066956971, 85644154810, 585021657, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 31 :=
  ⟨⟨93,19,86⟩,mass_cell 31 93 19 86 148 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 691239076770, 126788706738, 7200712725, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 31 :=
  ⟨⟨85,30,88⟩,mass_cell 31 85 30 88 131 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 737655684078, 86892087598, 941247600, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 31 :=
  ⟨⟨84,48,90⟩,mass_cell 31 84 48 90 119 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 782972177569, 43569337779, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 31 :=
  ⟨⟨94,15,85⟩,mass_cell 31 94 15 85 159 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 671013921731, 144781842175, 10364543887, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 31 :=
  ⟨⟨96,47,90⟩,mass_cell 31 96 47 90 119 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 782205480689, 44089448283, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 31 :=
  ⟨⟨89,24,87⟩,mass_cell 31 89 24 87 139 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 713875231426, 107679413850, 3547534558, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 31 :=
  ⟨⟨107,46,90⟩,mass_cell 31 107 46 90 120 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 781691193124, 44629211222, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 31 :=
  ⟨⟨100,18,86⟩,mass_cell 31 100 18 86 151 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 692019757304, 126252985780, 6261702653, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 31 :=
  ⟨⟨94,29,88⟩,mass_cell 31 94 29 88 132 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 737491117943, 87724313400, 1115732016, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 31 :=
  ⟨⟨89,37,89⟩,mass_cell 31 89 37 89 125 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 760686578484, 65481778000, 71753787, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 31 :=
  ⟨⟨118,45,90⟩,mass_cell 31 118 45 90 120 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 781074662904, 44981750830, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 31 :=
  ⟨⟨109,35,89⟩,mass_cell 31 109 35 89 127 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 759662252363, 66567047976, 149889336, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 31 :=
  ⟨⟨110,12,85⟩,mass_cell 31 110 12 85 170 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 678787073000, 141482509644, 3963707144, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 31 :=
  ⟨⟨117,15,86⟩,mass_cell 31 117 15 86 160 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 697801280678, 123825736702, 2337867673, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 31 :=
  ⟨⟨128,44,90⟩,mass_cell 31 128 44 90 121 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 780730162099, 45356152654, 24667, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 31 :=
  ⟨⟨127,33,89⟩,mass_cell 31 127 33 89 129 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 759136713171, 66857237970, 202398563, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 31 :=
  ⟨⟨133,6,85⟩,mass_cell 31 133 6 85 210 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 703027666661, 123179135686, 66045, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 31 :=
  ⟨⟨119,26,88⟩,mass_cell 31 119 26 88 137 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 737321199983, 87828987071, 1129847644, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 31 :=
  ⟨⟨118,20,87⟩,mass_cell 31 118 20 87 147 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 716139025684, 106703317062, 2103389979, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 31 :=
  ⟨⟨129,18,87⟩,mass_cell 31 129 18 87 152 (by decide)
    (by decide +kernel) [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 719555025287, 104915409422, 697639582, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 31) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42]

end Low6969Allocation.Group31
end Z6969Source2380
