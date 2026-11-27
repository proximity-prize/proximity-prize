import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0846

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles19
section Z6969Source2357
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group19
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27852344327, 62029834259, 87582401575, 31899170881, 77566731707, 38912111033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [68842498523], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [45016946699, 70653920283, 83287640115, 68926540231, 8797081029, 73070429675], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [53590696975, 83270588451, 49112524859, 73305315763, 56125530547], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [62097141779, 87481805863, 23309238337, 69077462435, 39012774305, 68775457259], by decide +kernel⟩
private def batches : List P := [p0]
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
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [66375597079, 87414766639, 6095884361, 64816053659, 26161429913, 73070427627], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [66392508443, 83136645171, 64782567843, 13243042209, 73036876275], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [66409419807, 70369186871, 60353385923, 4518891969], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 125 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [87414628387, 36210914365, 69161345423, 51981559183], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [87397919783, 23309238337, 69161348495, 39096660367], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87364433963, 10407562309, 64883161483, 30523505033], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [87347725359, 60588197259, 21933572489], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [74597044275, 60437270959, 8897744301], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61879983159, 55957757403, 123262425], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [49112524859], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤125) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 19 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤142 ∧ 5+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group19
end Z6969Source2357

-- Source: ProximityPrize.SubmissionLower.Low6969Mass20
section Z6969Source2358
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group20

private def m0 : MassCell 20 :=
  ⟨⟨1,3,10⟩,mass_cell 20 1 3 10 192 (by decide)
    (by decide +kernel) [4565332109981, 3791944996701, 3050088299781, 2410280185749, 1865498180109, 1408583759469, 1032242351541, 729043335141, 491420040189, 311669747709, 181953689829, 94297049781, 40588961901, 12582511629, 1894735509, 25840029] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 20 :=
  ⟨⟨1,6,36⟩,mass_cell 20 1 6 36 172 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3474746782181, 2735884997086, 1971353251390, 1361209409950, 889713106942, 540407340382, 296118472126, 138956227870, 50313697150, 10867333342, 577011028, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 20 :=
  ⟨⟨2,7,41⟩,mass_cell 20 2 7 41 166 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 2875220698590, 2039026827030, 1366303014186, 858817032646, 494531174250, 250694004630, 103840363210, 29791363206, 3654391626, 16557181, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 20 :=
  ⟨⟨1,9,47⟩,mass_cell 20 1 9 47 156 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 2987047363185, 2174169172963, 1385241287395, 810580007227, 419458468459, 178980303091, 54079639123, 7521100555, 67563002, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 20 :=
  ⟨⟨1,12,53⟩,mass_cell 20 1 12 53 143 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2383183645133, 1430532003072, 750343900368, 326259119712, 101755223472, 15230615232, 192971274, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 20 :=
  ⟨⟨5,13,55⟩,mass_cell 20 5 13 55 140 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2446288428578, 1455540433246, 729971742674, 297119283310, 82385599282, 9229448990, 22652760, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 20 :=
  ⟨⟨1,15,57⟩,mass_cell 20 1 15 57 134 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2503295481931, 1499581392823, 707510543743, 255575032471, 53934734143, 2573539107, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 20 :=
  ⟨⟨5,18,60⟩,mass_cell 20 5 18 60 127 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2559387479855, 1581953850510, 665986491294, 195830545326, 25333044414, 152951751, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 20 :=
  ⟨⟨6,21,62⟩,mass_cell 20 6 21 62 122 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1669522001475, 632703305739, 149682758907, 10415982099, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 20 :=
  ⟨⟨5,23,63⟩,mass_cell 20 5 23 63 118 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1718516847069, 614019650949, 124759848469, 5245629968, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 20 :=
  ⟨⟨1,26,64⟩,mass_cell 20 1 26 64 114 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1762935708237, 580576846420, 91510567348, 1363506142, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 20 :=
  ⟨⟨5,28,65⟩,mass_cell 20 5 28 65 112 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1814989414398, 569712026102, 76342652998, 525673693, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 20 :=
  ⟨⟨1,32,66⟩,mass_cell 20 1 32 66 108 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1861306079173, 534628876730, 49251471010, 11281699] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 20 :=
  ⟨⟨10,35,67⟩,mass_cell 20 10 35 67 106 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1910788975366, 516114163364, 36091201984, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 20 :=
  ⟨⟨13,40,68⟩,mass_cell 20 13 40 68 102 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1958846077485, 484253202882, 20442906170, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 20 :=
  ⟨⟨1,48,69⟩,mass_cell 20 1 48 69 98 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2008038018244, 444799665498, 7419193180, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 20 :=
  ⟨⟨46,32,67⟩,mass_cell 20 46 32 67 109 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1902822381821, 514956840025, 45646447189, 37505695, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 20 :=
  ⟨⟨44,28,66⟩,mass_cell 20 44 28 66 113 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1852409830987, 542580439801, 68418983989, 638055565, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 20 :=
  ⟨⟨61,36,68⟩,mass_cell 20 61 36 68 106 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1951037091417, 482679584248, 28530660712, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 20 :=
  ⟨⟨50,44,69⟩,mass_cell 20 50 44 69 101 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2002724245359, 448052610085, 11977276184, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 20 :=
  ⟨⟨67,30,67⟩,mass_cell 20 67 30 67 111 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1899038017909, 513024982128, 50743493280, 201353280, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 20 :=
  ⟨⟨55,27,66⟩,mass_cell 20 55 27 66 115 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1849378371963, 540152210911, 71364854263, 1010154752, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 20 :=
  ⟨⟨71,35,68⟩,mass_cell 20 71 35 68 107 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1949952319028, 482842577980, 30428182800, 460500] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 20 :=
  ⟨⟨72,42,69⟩,mass_cell 20 72 42 69 102 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2000662826198, 448361502816, 14299020432, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 20 :=
  ⟨⟨61,23,65⟩,mass_cell 20 61 23 65 120 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1795699793613, 561543078169, 97696574809, 4297395639, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 20 :=
  ⟨⟨69,22,65⟩,mass_cell 20 69 22 65 122 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1795218498648, 562655924964, 100465763252, 5218681988, 15805, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 20 :=
  ⟨⟨82,24,66⟩,mass_cell 20 82 24 66 120 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1845345585171, 537491612833, 77012855197, 2232842425, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 20 :=
  ⟨⟨77,18,64⟩,mass_cell 20 77 18 64 131 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1743270267641, 583033475466, 124953963066, 10788828138, 36361333, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 20 :=
  ⟨⟨77,29,67⟩,mass_cell 20 77 29 67 113 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1897326426078, 511032872682, 52351600382, 334068516, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 20 :=
  ⟨⟨69,52,70⟩,mass_cell 20 69 52 70 97 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2050586001828, 408964902114, 4069332257, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 20 :=
  ⟨⟨79,15,63⟩,mass_cell 20 79 15 63 140 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1694857702421, 605228997427, 147710125483, 15327601480, 2024786, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 20 :=
  ⟨⟨80,51,70⟩,mass_cell 20 80 51 70 97 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2049949563213, 409281203717, 4578434194, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 20 :=
  ⟨⟨77,21,65⟩,mass_cell 20 77 21 65 125 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1794502995195, 562083191907, 101326926003, 5721695979, 1514549, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 20 :=
  ⟨⟨97,18,65⟩,mass_cell 20 97 18 65 132 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1796753907881, 563444134000, 96859521520, 2868118320, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 20 :=
  ⟨⟨85,28,67⟩,mass_cell 20 85 28 67 114 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1897082739874, 512126166170, 54238554474, 492469727, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 20 :=
  ⟨⟨101,49,70⟩,mass_cell 20 101 49 70 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2048834388172, 409402548400, 5579381174, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 20 :=
  ⟨⟨95,15,64⟩,mass_cell 20 95 15 64 141 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1748740136199, 586707668087, 116169173087, 3689564993, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 20 :=
  ⟨⟨101,26,67⟩,mass_cell 20 101 26 67 117 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1896280679527, 510852452648, 54804812552, 614576922, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 20 :=
  ⟨⟨82,41,69⟩,mass_cell 20 82 41 69 103 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1999932855130, 448727189797, 15426929389, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 20 :=
  ⟨⟨105,3,61⟩,mass_cell 20 105 3 61 243 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1673162583600, 682807085436, 98961574280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 20 :=
  ⟨⟨111,48,70⟩,mass_cell 20 111 48 70 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2048358066900, 409208503482, 6040019916, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 20 :=
  ⟨⟨111,38,69⟩,mass_cell 20 111 38 69 105 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997855059789, 446731716928, 17806163792, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 20 :=
  ⟨⟨121,47,70⟩,mass_cell 20 121 47 70 100 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2047860070404, 408466887720, 6425290838, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 20 :=
  ⟨⟨119,37,69⟩,mass_cell 20 119 37 69 106 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997720950527, 447096890129, 18357551473, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 20 :=
  ⟨⟨90,33,68⟩,mass_cell 20 90 33 68 109 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1948106164717, 481930180605, 33350664501, 18426783, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 20 :=
  ⟨⟨123,12,65⟩,mass_cell 20 123 12 65 155 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1818121574957, 582875621418, 62387256415, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 20 :=
  ⟨⟨130,46,70⟩,mass_cell 20 130 46 70 100 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2047574069390, 408323593010, 6779694122, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 20 :=
  ⟨⟨115,30,68⟩,mass_cell 20 115 30 68 112 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1946798467594, 479672236038, 34409944902, 56610849, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 20 :=
  ⟨⟨134,9,65⟩,mass_cell 20 134 9 65 174 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1830600175539, 585484981275, 39628678003, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 20 :=
  ⟨⟨131,15,66⟩,mass_cell 20 131 15 66 143 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1861359413213, 552657814100, 47815911567, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 20 :=
  ⟨⟨130,21,67⟩,mass_cell 20 130 21 67 127 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1901909430391, 517271462016, 43733721583, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 20 :=
  ⟨⟨134,27,68⟩,mass_cell 20 134 27 68 117 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1948495949029, 481855148847, 31010685440, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 20 :=
  ⟨⟨127,36,69⟩,mass_cell 20 127 36 69 107 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997551798444, 446759578546, 18523577194, 71820] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 20 :=
  ⟨⟨138,45,70⟩,mass_cell 20 138 45 70 101 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2047504165769, 408869877017, 7102821054, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 20) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53]

end Low6969Allocation.Group20
end Z6969Source2358

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles20
section Z6969Source2359
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14680722439, 32365943823, 70115736599, 87195549743, 48037313895, 39447588199], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35018544487, 26361575783, 34883833271, 13090798071, 8779123191, 25958913543], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13074018823, 47299313191, 38709521959, 4349938215, 54972967, 4333158955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [28087425033, 40872915991, 87077903395, 35991629887, 39648845119, 35169469759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35001837887, 4618374599, 13258566107, 8896494043, 8829453787, 25975621123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17368982019, 122078743, 1099633707543, 1099633708567, 1099633709591, 4349934119], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4333158951, 47282468395, 34380932653, 12889465395, 4637235], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36577420303, 70048827417, 74243607601, 43792746843, 30975161691, 30690022747], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26260911451, 1100422238555, 8896493011, 8812675539, 4500934099, 17452865011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13090793971, 1099700817415, 1099684037131, 1099684038155, 1099684039179, 4366711327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [47316018723, 38709450277, 8644831783, 4333090343, 4299601459, 4636211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40788897811, 74243266593, 52886282297, 39564958027, 26680197451, 26411834699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17570314623, 4786146687, 4534417887, 4484153823, 1099868588511, 13208231399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8829382119, 1099767926263, 1099767927287, 1099667259919, 1099667260943, 43088163345], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [105298459, 1099616927259, 4366642723, 71677475, 34414485029, 21529657893], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12939794981], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53204302869, 86927044649, 14516864069, 31142867235, 30857793825, 34884399393], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13225013665, 8879718817, 43541085607, 30656391589, 1099935698383, 1099935699407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17486352867, 8913266147, 1099818254827, 1099818255851, 1099818256875, 4484084215], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767855607, 1099767922167, 17234692645, 54899237, 1099566528039, 8611274285], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299532849], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57398806553, 86893559853, 35169468701, 34917885213, 9332705565, 39330072977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30706725267, 17519977893, 8913271205, 8829453733, 1099918922195, 17469575651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851810275, 1099851811299, 1099851812323, 1099767855607, 1099767922167, 1099767923191], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8779048441, 4433752569, 88453661, 1099600082463, 17217983019, 4333086249], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38121001, 30086033967], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61576467485, 69831200817, 26512494909, 26294463805, 9181710653, 39397184891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26462092665, 8913268157, 8795830717, 1100002805183, 1099935697359, 1099935698383], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935699407, 13141121521, 4567968241, 1099784632819, 1099784699379, 1099784700403], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [155562509, 1099667191311, 21546434081, 12956571169, 38675895853, 4299531825], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69965144097, 48524207161, 35320389967, 22385231181, 26327948621, 17536760173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4735815021, 4551195077, 1099969249735, 1099969250759, 1099969251783, 13208231381], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812604885, 1099885366747, 1099885367771, 1099700746759, 1099700813319, 4383419917], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667191311, 8644828709, 4349864485, 54899237, 17217914409, 8628050473], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78387375141, 27200370753, 31176420651, 26646711593, 26395126057, 8829453721], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153803163, 8946821569, 8812606913, 1099986026947, 1099902141911, 1099902142935], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099902143959, 1099751077371, 1099751078395, 1099751144955, 17402465789, 8812601853], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349865497, 38121001, 38122025], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78353889321, 14449755205, 31059048741, 30740355365, 26277689637, 8896493985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002805183, 1100002806207, 1100002807231, 1100002808255, 13325670857, 8930044361], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4584748489, 1099801476591, 1099801477615, 1099650414099, 1099650480659, 25891731989], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13006902805, 4383418909, 88453661], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74075767853, 5943708741, 30891279661, 26378282285, 17721311533, 1100053070259], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053136819, 1100053137843, 13208233409, 8812606913, 1099918921171, 1099918922195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21730985461, 13090790901, 1099751077371, 1099751078395, 1099751144955, 4400197137], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8628051497, 4333087273, 21344813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65553010737, 1665519689, 26529272129, 22049828161, 13392790849, 1100002805183], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002806207, 1100002807231, 8862936525, 4517640653, 1099935695311, 1099885367771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17402466809, 8795825657, 1099700746759, 1099700813319, 138785297, 1099650414099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4316309037, 21343789, 17184428593], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [57013410869, 22133644625, 17704531281, 9064270161, 1099969251783, 1099969252807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099969253831, 4567971281, 1099918851539, 1099918918099, 1099918919123, 13141122545], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4551192049, 1099633636887, 1099633703447, 8594497073, 4299532849, 4567601], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [44246018105, 17704528241, 13275348337, 4719037809, 1099918851539, 1099918918099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099918919123, 1099918920147, 1099885366747, 1099885367771, 8795826673, 4433753585], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099633636887, 1099633703447, 4349864485, 54899237], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 20 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 6+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group20
end Z6969Source2359

-- Source: ProximityPrize.SubmissionLower.Low6969Mass21
section Z6969Source2360
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group21

private def m0 : MassCell 21 :=
  ⟨⟨1,3,10⟩,mass_cell 21 1 3 10 192 (by decide)
    (by decide +kernel) [4565332109981, 3791944996701, 3050088299781, 2410280185749, 1865498180109, 1408583759469, 1032242351541, 729043335141, 491420040189, 311669747709, 181953689829, 94297049781, 40588961901, 12582511629, 1894735509, 25840029] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 21 :=
  ⟨⟨1,6,36⟩,mass_cell 21 1 6 36 172 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3474746782181, 2735884997086, 1971353251390, 1361209409950, 889713106942, 540407340382, 296118472126, 138956227870, 50313697150, 10867333342, 577011028, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 21 :=
  ⟨⟨1,9,47⟩,mass_cell 21 1 9 47 156 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 2987047363185, 2174169172963, 1385241287395, 810580007227, 419458468459, 178980303091, 54079639123, 7521100555, 67563002, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 21 :=
  ⟨⟨1,12,53⟩,mass_cell 21 1 12 53 143 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2383183645133, 1430532003072, 750343900368, 326259119712, 101755223472, 15230615232, 192971274, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 21 :=
  ⟨⟨5,13,55⟩,mass_cell 21 5 13 55 140 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2446288428578, 1455540433246, 729971742674, 297119283310, 82385599282, 9229448990, 22652760, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 21 :=
  ⟨⟨1,15,57⟩,mass_cell 21 1 15 57 134 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2503295481931, 1499581392823, 707510543743, 255575032471, 53934734143, 2573539107, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 21 :=
  ⟨⟨5,18,60⟩,mass_cell 21 5 18 60 127 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2559387479855, 1581953850510, 665986491294, 195830545326, 25333044414, 152951751, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 21 :=
  ⟨⟨6,21,62⟩,mass_cell 21 6 21 62 122 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1669522001475, 632703305739, 149682758907, 10415982099, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 21 :=
  ⟨⟨5,23,63⟩,mass_cell 21 5 23 63 118 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1718516847069, 614019650949, 124759848469, 5245629968, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 21 :=
  ⟨⟨9,25,64⟩,mass_cell 21 9 25 64 116 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1764196859450, 591459217228, 101789968272, 2393610858, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 21 :=
  ⟨⟨1,29,65⟩,mass_cell 21 1 29 65 111 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1808895196521, 550924997701, 66210917405, 217255117, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 21 :=
  ⟨⟨9,31,66⟩,mass_cell 21 9 31 66 109 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1862114048849, 543935417080, 55516282444, 56232958, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 21 :=
  ⟨⟨10,35,67⟩,mass_cell 21 10 35 67 106 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1910788975366, 516114163364, 36091201984, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 21 :=
  ⟨⟨13,40,68⟩,mass_cell 21 13 40 68 102 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1958846077485, 484253202882, 20442906170, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 21 :=
  ⟨⟨12,47,69⟩,mass_cell 21 12 47 69 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2007241061793, 447966796906, 8579964743, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 21 :=
  ⟨⟨53,21,64⟩,mass_cell 21 53 21 64 124 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1745953397883, 584384503473, 121430054241, 8541630513, 1407326, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 21 :=
  ⟨⟨67,30,67⟩,mass_cell 21 67 30 67 111 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1899038017909, 513024982128, 50743493280, 201353280, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 21 :=
  ⟨⟨38,38,68⟩,mass_cell 21 38 38 68 104 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1954596841678, 484083866570, 24632861936, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 21 :=
  ⟨⟨25,46,69⟩,mass_cell 21 25 46 69 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2005672979394, 448369919260, 9699255256, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 21 :=
  ⟨⟨38,45,69⟩,mass_cell 21 38 45 69 100 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2004045093284, 448013675874, 10818092512, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 21 :=
  ⟨⟨55,27,66⟩,mass_cell 21 55 27 66 115 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1849378371963, 540152210911, 71364854263, 1010154752, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 21 :=
  ⟨⟨71,35,68⟩,mass_cell 21 71 35 68 107 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1949952319028, 482842577980, 30428182800, 460500] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 21 :=
  ⟨⟨61,43,69⟩,mass_cell 21 61 43 69 101 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2001718541654, 448575106934, 13174377259, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 21 :=
  ⟨⟨72,42,69⟩,mass_cell 21 72 42 69 102 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2000662826198, 448361502816, 14299020432, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 21 :=
  ⟨⟨61,23,65⟩,mass_cell 21 61 23 65 120 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1795699793613, 561543078169, 97696574809, 4297395639, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 21 :=
  ⟨⟨77,18,64⟩,mass_cell 21 77 18 64 131 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1743270267641, 583033475466, 124953963066, 10788828138, 36361333, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 21 :=
  ⟨⟨69,52,70⟩,mass_cell 21 69 52 70 97 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2050586001828, 408964902114, 4069332257, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 21 :=
  ⟨⟨82,24,66⟩,mass_cell 21 82 24 66 120 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1845345585171, 537491612833, 77012855197, 2232842425, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 21 :=
  ⟨⟨81,34,68⟩,mass_cell 21 81 34 68 108 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1948785447271, 482001293168, 31961073968, 5232577] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 21 :=
  ⟨⟨77,21,65⟩,mass_cell 21 77 21 65 125 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1794502995195, 562083191907, 101326926003, 5721695979, 1514549, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 21 :=
  ⟨⟨80,51,70⟩,mass_cell 21 80 51 70 97 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2049949563213, 409281203717, 4578434194, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 21 :=
  ⟨⟨91,50,70⟩,mass_cell 21 91 50 70 98 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2049289227561, 409085897798, 5073468307, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 21 :=
  ⟨⟨97,18,65⟩,mass_cell 21 97 18 65 132 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1796753907881, 563444134000, 96859521520, 2868118320, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 21 :=
  ⟨⟨85,28,67⟩,mass_cell 21 85 28 67 114 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1897082739874, 512126166170, 54238554474, 492469727, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 21 :=
  ⟨⟨101,49,70⟩,mass_cell 21 101 49 70 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2048834388172, 409402548400, 5579381174, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 21 :=
  ⟨⟨95,15,64⟩,mass_cell 21 95 15 64 141 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1748740136199, 586707668087, 116169173087, 3689564993, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 21 :=
  ⟨⟨108,25,67⟩,mass_cell 21 108 25 67 119 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1896549416184, 510905613345, 53978082937, 432695250, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 21 :=
  ⟨⟨82,41,69⟩,mass_cell 21 82 41 69 103 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1999932855130, 448727189797, 15426929389, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 21 :=
  ⟨⟨111,38,69⟩,mass_cell 21 111 38 69 105 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997855059789, 446731716928, 17806163792, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 21 :=
  ⟨⟨111,48,70⟩,mass_cell 21 111 48 70 99 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2048358066900, 409208503482, 6040019916, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 21 :=
  ⟨⟨104,13,64⟩,mass_cell 21 104 13 64 149 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1756971951498, 593979991262, 104122619597, 310584372, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 21 :=
  ⟨⟨114,24,67⟩,mass_cell 21 114 24 67 121 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1897567188157, 512511643305, 52788241125, 163900376, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 21 :=
  ⟨⟨121,47,70⟩,mass_cell 21 121 47 70 100 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2047860070404, 408466887720, 6425290838, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 21 :=
  ⟨⟨90,33,68⟩,mass_cell 21 90 33 68 109 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1948106164717, 481930180605, 33350664501, 18426783, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 21 :=
  ⟨⟨115,30,68⟩,mass_cell 21 115 30 68 112 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1946798467594, 479672236038, 34409944902, 56610849, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 21 :=
  ⟨⟨127,36,69⟩,mass_cell 21 127 36 69 107 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997551798444, 446759578546, 18523577194, 71820] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 21 :=
  ⟨⟨119,9,64⟩,mass_cell 21 119 9 64 173 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1777602658860, 607049899134, 68923911930, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 21 :=
  ⟨⟨120,13,65⟩,mass_cell 21 120 13 65 150 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1812736991234, 576574760946, 67335251350, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 21 :=
  ⟨⟨128,28,68⟩,mass_cell 21 128 28 68 115 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1947778420607, 481194033313, 32826006414, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 21 :=
  ⟨⟨134,35,69⟩,mass_cell 21 134 35 69 108 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1997741640660, 447408259501, 18525224976, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 21 :=
  ⟨⟨138,45,70⟩,mass_cell 21 138 45 70 101 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2047504165769, 408869877017, 7102821054, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 21 :=
  ⟨⟨128,6,64⟩,mass_cell 21 128 6 64 200 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1796537509013, 616088668754, 45732451116, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 21 :=
  ⟨⟨123,12,65⟩,mass_cell 21 123 12 65 155 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1818121574957, 582875621418, 62387256415, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 21 :=
  ⟨⟨135,20,67⟩,mass_cell 21 135 20 67 129 (by decide)
    (by decide +kernel) [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1903521371544, 517976852328, 39345879125, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 21) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53]

end Low6969Allocation.Group21
end Z6969Source2360

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles21
section Z6969Source2361
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10922626053, 28087425035, 49060197399, 87128302631, 27468806211, 35320390991], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35102427471, 39162588495, 43390088651, 39078552011, 13275344331, 8846163419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795900379, 21680654851, 17352204803, 1099667261967, 1099667262991, 1099667264015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4400266779, 105301531, 8628123179, 12906242607, 4316312111, 34364154419], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [28053870603, 40755475479, 87027571747, 35907743807, 35437763891, 30958387507], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34968215859, 13124421043, 17519976903, 8913270215, 8846229959, 1099801480687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099801481711, 1099700814343, 1099700815367, 1099700816391, 21647098379, 17318648331], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43104941583, 4366644759, 122076695, 4400197147, 4316378667, 42970651183], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12906240559, 4316310063, 4634163, 4635187], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36459979791, 69981718553, 74176498737, 39615220043, 30924763467, 30690021707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30505546059, 1100489347403, 13157904823, 8795832759, 1100036361655, 17452798435], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8896488931, 1099818254827, 1099818255851, 1099818256875, 4450529787, 1099751078395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099751144955, 43138426375, 25874952729, 17285090843, 71676451, 1099583305251], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644829735, 21343789, 38659117619], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36628148243, 86910063645, 44296349753, 35555136787, 31059048723, 35018545427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13225016703, 4685483391, 13325605299, 13191457203, 8812607923, 1099918919123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918920147, 1099868589535, 1099868590559, 1099818187243, 1099818253803, 1099818254827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4484082175, 1099734299135, 1099734300159, 21680650753, 13090787841, 4383416861], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21342765, 21343791, 42953945651, 34364153395], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48959667221, 82632010789, 22955801665, 31092534559, 30807461149, 30606208285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8963599779, 8846162337, 1100103468455, 1100103469479, 1100103470503, 1100103471527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39195786673, 30606058931, 13292047825, 8963595731, 8812603859, 1099851741667], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851742691, 1099851809251, 1099734300159, 4383418891, 1099683967499, 17301800471], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71674401, 1099583303203, 4316306989, 21341741], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53137393689, 86843227181, 1615188041, 26797636883, 30740355345, 26311244049], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13090797973, 1100170578327, 1100170579351, 39296518555, 26394980763, 9080969655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8946820533, 8812605877, 1099952405963, 1099952472523, 1099952473547, 1099935699407], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801407983, 1099801409007, 1099801410031, 13057166857, 4400195087, 1099667189263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38118953, 38119979, 4316306989, 25774289459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57298277405, 74025503793, 26546048293, 30555875621, 9181710629, 35118994815], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22234233215, 13191457181, 8812607901, 1100137022879, 1100036360631, 1100036361655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100036362679, 1099902073303, 1099902074327, 1099902140887, 13157831137, 4618297825], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4484082153, 1099818185195, 1099818186219, 1099616856603, 1099616857627, 8644825637], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349861413, 4564529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65670176801, 52701732921, 31025422669, 22318121293, 22049757517, 21848502609], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8980384081, 8829383085, 1100069846447, 1100069847471, 1100069914031, 1100053137843], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100053138867, 1100053139891, 8946817497, 4601521625, 4484083161, 1099818186219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099818187243, 1099683966475, 1099683967499, 17285022233, 8695158297, 54896165], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099566524967, 4563505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78320266277, 27116484673, 31109311769, 26562759961, 30555810073, 1100237687175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237688199, 1100237689223, 13225011601, 8846162321, 1100187288979, 1099918850515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918851539, 1099918918099, 13258493401, 8896486873, 4500859365, 1099834962407], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834963431, 25891663381, 13006834197, 1099616856603, 1099616857627, 4349861413], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54896165], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78286780457, 14349091909, 31008717077, 26495719701, 26277688597, 8896492945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100187287955, 1100103468455, 1100103469479, 1100103470503, 1100103471527, 9047480773], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8879711685, 4534415813, 1099868518879, 1099868519903, 21714205177, 13073945081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717521923, 1099717522947, 4383417869, 1099667189263, 54896165, 54897189], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12923015721], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69764023341, 10087680069, 26613089577, 22133645609, 21932390697, 8829385113], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153800091, 1100069915055, 1100069916079, 1100069917103, 8913265097, 4567969225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952403915, 1099902073303, 1099902074327, 1099902140887, 17436018165, 8846154229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667189263, 1099667190287, 4349863449, 38118953, 38119977], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69713760305, 26546049313, 26294463777, 9164933409, 8930045345, 8795830689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100120245667, 1100069915055, 1100069916079, 1100069917103, 1099902073303, 1099902074327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099902140887, 13224939997, 8846156253, 1099767852535, 1099767853559, 1099767854583], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4383416861, 88451613, 12889461297], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56929524789, 22100090173, 17670976829, 9047492925, 1100069915055, 1100069916079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069917103, 4567971253, 1100036292023, 1100036293047, 1100036359607, 8946818517], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4601522645, 4484084181, 1099751078395, 1099700744711, 1099700745735, 71674401], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099583303203, 4316306989, 21341741], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 21 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group21
end Z6969Source2361

-- Source: ProximityPrize.SubmissionLower.Low6969Mass22
section Z6969Source2362
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group22

private def m0 : MassCell 22 :=
  ⟨⟨1,3,17⟩,mass_cell 22 1 3 17 199 (by decide)
    (by decide +kernel) [4550535358424, 3870640287910, 3098030671653, 2429895364629, 1867812790605, 1401830384973, 1022222331285, 719489561253, 484359754749, 307787339805, 180953492613, 95266137525, 42359947053, 14096341869, 2563490805, 78268150, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 22 :=
  ⟨⟨1,6,41⟩,mass_cell 22 1 6 41 177 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2783053190120, 2012323800688, 1387966180912, 908967140080, 555748576432, 308875715440, 149057109808, 57144639472, 14133511600, 1162260592, 71488, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 22 :=
  ⟨⟨1,8,49⟩,mass_cell 22 1 8 49 165 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2183943656887, 1433408688475, 877938150239, 488441565379, 235638791815, 90060022187, 22045783855, 1746938899, 35080, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 22 :=
  ⟨⟨2,9,52⟩,mass_cell 22 2 9 52 161 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2272361858142, 1460276495715, 863009659083, 456376549251, 203532534219, 67702965987, 12183180555, 351235130, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 22 :=
  ⟨⟨4,12,58⟩,mass_cell 22 4 12 58 148 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2410085843286, 1557412151634, 830984985306, 376457478498, 129134182122, 25045241202, 951980202, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 22 :=
  ⟨⟨1,14,60⟩,mass_cell 22 1 14 60 141 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2434734581855, 1609887839368, 812065829032, 332405934536, 92674453480, 10435187464, 25761751, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 22 :=
  ⟨⟨1,15,61⟩,mass_cell 22 1 15 61 138 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1641686176612, 802258414408, 310697143876, 77159954008, 6235387012, 177168, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 22 :=
  ⟨⟨1,17,63⟩,mass_cell 22 1 17 63 133 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1724219939115, 797988562475, 277794710731, 54302811595, 2022801118, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 22 :=
  ⟨⟨1,18,64⟩,mass_cell 22 1 18 64 131 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1767406299296, 803459212348, 265984393180, 46069788028, 1089490632, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 22 :=
  ⟨⟨1,21,66⟩,mass_cell 22 1 21 66 126 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1844237784128, 797445076782, 223064591034, 24817913022, 52192650, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 22 :=
  ⟨⟨1,23,67⟩,mass_cell 22 1 23 67 122 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1880405282156, 791201996671, 196560415207, 15477736871, 106073, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 22 :=
  ⟨⟨2,25,68⟩,mass_cell 22 2 25 68 120 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1916714233613, 792562130047, 175051269351, 9592726434, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 22 :=
  ⟨⟨1,28,69⟩,mass_cell 22 1 28 69 116 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1949938864539, 785288510875, 143785086695, 4019234764, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 22 :=
  ⟨⟨1,31,70⟩,mass_cell 22 1 31 70 113 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1982107992839, 790769564958, 120530706578, 1535584365, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 22 :=
  ⟨⟨1,35,71⟩,mass_cell 22 1 35 71 110 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2009983710729, 793081032558, 93431339850, 262116474, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 22 :=
  ⟨⟨3,40,72⟩,mass_cell 22 3 40 72 106 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2032455268574, 797377376143, 67379408459, 2973065] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 22 :=
  ⟨⟨14,46,73⟩,mass_cell 22 14 46 73 103 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 805211051964, 44912960584, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 22 :=
  ⟨⟨61,22,69⟩,mass_cell 22 61 22 69 126 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1943393300002, 769688040972, 166039058988, 14037569356, 33558650, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 22 :=
  ⟨⟨37,32,71⟩,mass_cell 22 37 32 71 113 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2008181268645, 781806039295, 103926039011, 1146133419, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 22 :=
  ⟨⟨57,30,71⟩,mass_cell 22 57 30 71 115 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2007463109718, 777216792408, 109399794072, 2125984336, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 22 :=
  ⟨⟨28,38,72⟩,mass_cell 22 28 38 72 108 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031986668220, 790737806202, 73145348026, 49359800] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 22 :=
  ⟨⟨26,45,73⟩,mass_cell 22 26 45 73 104 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 803316807369, 47045111409, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 22 :=
  ⟨⟨46,27,70⟩,mass_cell 22 46 27 70 119 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1978216068825, 776031909691, 135728299003, 5193832204, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 22 :=
  ⟨⟨70,34,72⟩,mass_cell 22 70 34 72 112 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031392531927, 781414482904, 82210688984, 502210803, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 22 :=
  ⟨⟨70,41,73⟩,mass_cell 22 70 41 73 107 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 795630753754, 54300837566, 4901840] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 22 :=
  ⟨⟨64,25,70⟩,mass_cell 22 64 25 70 122 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1977294952942, 772148397385, 140019643337, 7295588041, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 22 :=
  ⟨⟨79,33,72⟩,mass_cell 22 79 33 72 113 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031309028397, 779947908556, 83693201584, 687468233, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 22 :=
  ⟨⟨75,17,68⟩,mass_cell 22 75 17 68 138 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1907466320230, 772406262110, 192851508698, 22992186606, 203319342, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 22 :=
  ⟨⟨75,28,71⟩,mass_cell 22 75 28 71 118 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2006980871850, 773327658517, 112421687465, 3139721879, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 22 :=
  ⟨⟨77,50,74⟩,mass_cell 22 77 50 74 102 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 819367475280, 30649177933, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 22 :=
  ⟨⟨72,24,70⟩,mass_cell 22 72 24 70 124 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1977068851716, 771171517644, 141211338540, 8081598156, 987642, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 22 :=
  ⟨⟨88,18,69⟩,mass_cell 22 88 18 69 136 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1943828201092, 771600484684, 165186357868, 11858511441, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 22 :=
  ⟨⟨87,49,74⟩,mass_cell 22 87 49 74 103 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 818407697613, 31671052997, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 22 :=
  ⟨⟨97,38,73⟩,mass_cell 22 97 38 73 109 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 792826530028, 58228489164, 65658224, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 22 :=
  ⟨⟨96,48,74⟩,mass_cell 22 96 48 74 103 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 818148272688, 32727029500, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 22 :=
  ⟨⟨93,21,70⟩,mass_cell 22 93 21 70 130 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1977092649570, 770713732110, 139565609490, 6946696725, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 22 :=
  ⟨⟨95,31,72⟩,mass_cell 22 95 31 72 115 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031230873540, 778812971422, 85734978394, 1027693802, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 22 :=
  ⟨⟨106,47,74⟩,mass_cell 22 106 47 74 104 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 816519302980, 33356217242, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 22 :=
  ⟨⟨105,3,66⟩,mass_cell 22 105 3 66 248 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1868148339862, 851242971405, 173497912072, 34911665, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 22 :=
  ⟨⟨114,46,74⟩,mass_cell 22 114 46 74 104 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 816701411116, 34242144028, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 22 :=
  ⟨⟨113,36,73⟩,mass_cell 22 113 36 73 111 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 791650047555, 59341677759, 128310900, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 22 :=
  ⟨⟨121,35,73⟩,mass_cell 22 121 35 73 112 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 790409757451, 58924966075, 128782906, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 22 :=
  ⟨⟨123,45,74⟩,mass_cell 22 123 45 74 105 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 815487293012, 34603460168, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 22 :=
  ⟨⟨124,14,70⟩,mass_cell 22 124 14 70 151 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1981677000834, 797739158216, 115710881017, 455126, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 22 :=
  ⟨⟨118,6,68⟩,mass_cell 22 118 6 68 204 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1927562583990, 831693818140, 134760479441, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 22 :=
  ⟨⟨103,30,72⟩,mass_cell 22 103 30 72 116 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031189699822, 777381786048, 85348246368, 1060870496, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 22 :=
  ⟨⟨131,44,74⟩,mass_cell 22 131 44 74 106 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 815069507283, 34951283991, 38598] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 22 :=
  ⟨⟨131,12,70⟩,mass_cell 22 131 12 70 160 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 1983444678993, 806762852043, 103544601017, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 22 :=
  ⟨⟨103,24,71⟩,mass_cell 22 103 24 71 125 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2007026611225, 774243638725, 112884710593, 2906102358, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 22 :=
  ⟨⟨127,26,72⟩,mass_cell 22 127 26 72 122 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2031390604849, 782266259228, 81842957600, 99499760, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 22 :=
  ⟨⟨132,18,71⟩,mass_cell 22 132 18 71 138 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2008763711309, 790331069414, 94489677398, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 22 :=
  ⟨⟨134,33,73⟩,mass_cell 22 134 33 73 114 (by decide)
    (by decide +kernel) [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 791448114500, 57993472880, 28206207, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 22) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51]

end Low6969Allocation.Group22
end Z6969Source2362

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles22
section Z6969Source2363
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group22
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19009702919, 36543995919, 82833261595, 65872041015, 43910448451, 39548580163], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26361829779, 21932651923, 4887072147, 34800274879, 13040793091, 8712275459], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47299572251, 34414817819, 25824957979, 12906574371, 4316644899, 21679651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21680675], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 137 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 137 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 137 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32164616203, 44950108183, 87078233127, 27452356675, 39548511555, 30891609411], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39162850627, 13292383679, 13091126743, 4517973463, 47450569207, 43105131011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25892064779, 13007170059, 4417306123, 4366976523, 1099617193487, 1099617194511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [34414815771, 38454815, 1099550083615, 4316641827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 137 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 137 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 137 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36611302415, 61610149915, 82733073455, 30908384575, 30690354495, 13560825151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43642079615, 30774097279, 13208495575, 8829646295, 8762606039, 1099801742819], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099801743843, 155894275, 1099667523075, 1099667524099, 17302132235, 4383749651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [88784403, 42954344999, 8594762279], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 137 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 137 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 137 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40822779923, 86910326817, 40068754495, 39732992279, 35220062487, 34985256215], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8913602963, 13325936047, 13158167983, 8829715887, 1099801743843, 26026213863], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13158161895, 1099768186347, 1099768187371, 1099768188395, 4501190131, 4417306099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099600412179, 1099600413203, 47299572251, 34414748187, 4350127643, 21479654951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4896295, 4897319], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 137 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 137 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 137 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40806202391, 82649048101, 31512376383, 35421316387, 30908385571, 30656801059], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8829716891, 9030969779, 8879977907, 8796160435, 1099852074455, 1099852075479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099784962535, 1099784963559, 1099784964583, 21680916975, 8829641199, 4417304059], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701075451, 43004608027, 55227931, 1099566856731, 4333350431, 34381261347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17201466915], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53187987483, 82598853677, 5927193671, 26831453471, 30740617503, 26294728991], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8896756127, 8812938655, 39196117413, 30589546919, 13309155779, 8930306499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4585010627, 1099885629903, 1099852072407, 1099852073431, 1099852074455, 1099768184299], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099768185323, 122336779, 1099633965579, 4366903831, 4333416983, 17218245151], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21672483, 30069518887], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53154567199, 78287112241, 26697304351, 26428941599, 17755128093, 39212963235], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26311425443, 4568301995, 1100036622763, 1100036623787, 1100036624811, 8980637119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8829645247, 4517969343, 1099751409135, 1099717852663, 1099717853687, 189379067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [189445627, 1099701074427, 13057497599, 4333349407, 21479587365, 12889724455], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65687216161, 52718772281, 35253543251, 22368781651, 22050020691, 17604130135], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9014266197, 4568233407, 1099952733631, 1099952734655, 1099952735679, 1099952736703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099952737727, 1099952738751, 13124607455, 4534676959, 1099667518979, 1099667520003], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8645090841, 4350126619, 55226907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78337305637, 27150366785, 31176682783, 26646973727, 26361833757, 8812938639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100154065295, 8980638127, 8812869039, 1100019843503, 1099919181255, 1099919182279], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099919183303, 1099784893927, 1099784960487, 1099784961511, 17402793459, 8812863987], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [105491981, 105558543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78303819817, 14366131269, 31076088091, 26512759067, 26277950745, 8913532311], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8812937623, 1100036623787, 1100036624811, 13258824143, 8846420431, 1099885625807], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885626831, 1099885627855, 1099784893927, 1099784960487, 1099784961511, 25875216911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12990387725, 4400458255, 105558543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69781062701, 10104719429, 26663683375, 26344988973, 21899099437, 8812871061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100003068339, 1100003069363, 1100003070387, 9047744955, 8879975867, 4517902779], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885625807, 1099885626831, 1099734628851, 1099734629875, 4400459267, 1099667518979], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21613807111, 8728976901, 38383133, 38449693], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69730799665, 26579865895, 26294725925, 9165195557, 8963861927, 8796092837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053398951, 1100003068339, 1100003069363, 1100003070387, 1099835292123, 1099835293147], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835294171, 17436348907, 8796087787, 155824643, 1099667518979, 4333348381], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38383133], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56946564149, 22117129537, 17671238977, 9081375041, 4585010619, 4517969339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099969512891, 1099969513915, 1099969514939, 1099969515963, 13158161887, 4568231391], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099734629875, 1099734630899, 155891203, 1099667520003, 8611536417, 4316572195], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21672481], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 22 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group22
end Z6969Source2363

-- Source: ProximityPrize.SubmissionLower.Low6969Mass23
section Z6969Source2364
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group23

private def m0 : MassCell 23 :=
  ⟨⟨1,3,24⟩,mass_cell 23 1 3 24 206 (by decide)
    (by decide +kernel) [4523726644349, 3866465157705, 3141976610172, 2443721028600, 1863283147500, 1387810545240, 1005040345404, 703299216792, 471503373420, 299158574520, 176360124540, 93792873144, 42731215212, 15039090840, 3169985340, 166938488, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 23 :=
  ⟨⟨2,6,48⟩,mass_cell 23 2 6 48 184 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2765563894125, 2095396982222, 1440155741342, 943048660334, 579627497534, 326733956366, 162499685342, 66346278062, 18985273214, 2418154574, 15515259, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 23 :=
  ⟨⟨2,8,55⟩,mass_cell 23 2 8 55 171 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2247163732003, 1510739103551, 930583308179, 525365147847, 261354120155, 106450844111, 30187060131, 3725630039, 19486357, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 23 :=
  ⟨⟨3,9,58⟩,mass_cell 23 3 9 58 167 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2291959016138, 1564106895680, 933352190348, 504163084136, 234716749844, 85499832272, 19308448220, 1248186488, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 23 :=
  ⟨⟨1,12,63⟩,mass_cell 23 1 12 63 153 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1697664681534, 939627754518, 448945813470, 169311044262, 40502494830, 3024807222, 2878, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 23 :=
  ⟨⟨3,14,66⟩,mass_cell 23 3 14 66 147 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1784109545753, 958999466386, 419627290898, 135561741970, 22978000402, 537070735, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 23 :=
  ⟨⟨2,15,67⟩,mass_cell 23 2 15 67 144 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1811077105856, 969313563833, 408007699601, 121780308353, 16797371657, 153013849, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 23 :=
  ⟨⟨5,17,69⟩,mass_cell 23 5 17 69 139 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1857801120492, 988352872366, 379218579674, 94804753294, 8174753866, 1426219, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 23 :=
  ⟨⟨1,21,71⟩,mass_cell 23 1 21 71 131 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1894795725605, 1008674730888, 327030534924, 54230295048, 1090838850, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 23 :=
  ⟨⟨3,22,72⟩,mass_cell 23 3 22 72 129 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1908191748677, 1044388498360, 326339071304, 49857835480, 718304458, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 23 :=
  ⟨⟨5,24,73⟩,mass_cell 23 5 24 73 127 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1071087197348, 306020029700, 37358039972, 167385420, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 23 :=
  ⟨⟨1,27,74⟩,mass_cell 23 1 27 74 123 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1107678435007, 281689622599, 23858766535, 1778995, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 23 :=
  ⟨⟨3,30,75⟩,mass_cell 23 3 30 75 119 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1142227031992, 257190182856, 14701072672, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 23 :=
  ⟨⟨2,34,76⟩,mass_cell 23 2 34 76 116 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1178345487486, 230028215176, 7337537497, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 23 :=
  ⟨⟨3,39,77⟩,mass_cell 23 3 39 77 112 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1213219422209, 199536758505, 2670512814, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 23 :=
  ⟨⟨12,45,78⟩,mass_cell 23 12 45 78 109 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1246664368557, 167557194023, 578896829, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 23 :=
  ⟨⟨37,36,77⟩,mass_cell 23 37 36 77 115 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1205129830007, 204133758358, 4811650668, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 23 :=
  ⟨⟨23,44,78⟩,mass_cell 23 23 44 78 110 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1244986598473, 169576669094, 798094816, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 23 :=
  ⟨⟨59,50,79⟩,mass_cell 23 59 50 79 107 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1276956934559, 138293795128, 118502233] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 23 :=
  ⟨⟨45,30,76⟩,mass_cell 23 45 30 76 120 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1166077702133, 235514096610, 13018089282, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 23 :=
  ⟨⟨56,34,77⟩,mass_cell 23 56 34 77 117 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1201850901849, 206707400256, 6429519754, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 23 :=
  ⟨⟨45,42,78⟩,mass_cell 23 45 42 78 111 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1241136069915, 172095539616, 1340438878, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 23 :=
  ⟨⟨69,49,79⟩,mass_cell 23 69 49 79 108 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1275873387633, 139194857901, 176322423] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 23 :=
  ⟨⟨53,25,75⟩,mass_cell 23 53 25 75 127 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1126457028787, 262896282583, 25405550199, 101450901, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 23 :=
  ⟨⟨65,33,77⟩,mass_cell 23 65 33 77 118 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1200358136307, 207285028370, 7174643529, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 23 :=
  ⟨⟨64,40,78⟩,mass_cell 23 64 40 78 112 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1238718416911, 174646832841, 2010262577, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 23 :=
  ⟨⟨66,17,73⟩,mass_cell 23 66 17 73 143 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1049426391969, 306225394409, 52064918129, 2281002294, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 23 :=
  ⟨⟨63,28,76⟩,mass_cell 23 63 28 76 123 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1162099438749, 235940513850, 15393653770, 2970659, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 23 :=
  ⟨⟨73,39,78⟩,mass_cell 23 73 39 78 113 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1237647850643, 175479495726, 2358417514, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 23 :=
  ⟨⟨71,27,76⟩,mass_cell 23 71 27 76 125 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1160907538623, 235908536640, 16207868652, 12429440, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 23 :=
  ⟨⟨75,22,75⟩,mass_cell 23 75 22 75 132 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1124322199005, 263282160970, 27602566250, 280061178, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 23 :=
  ⟨⟨77,18,74⟩,mass_cell 23 77 18 74 141 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1089022919316, 286955642292, 38022305748, 442192026, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 23 :=
  ⟨⟨78,48,79⟩,mass_cell 23 78 48 79 108 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1275204887845, 140318973171, 248523129] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 23 :=
  ⟨⟨88,47,79⟩,mass_cell 23 88 47 79 109 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1273929120345, 140464063407, 326540016, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 23 :=
  ⟨⟨81,21,75⟩,mass_cell 23 81 21 75 135 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1125129734135, 263567503368, 26947154412, 146106445, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 23 :=
  ⟨⟨89,30,77⟩,mass_cell 23 89 30 77 121 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1197585268631, 207385981866, 8574765642, 4627, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 23 :=
  ⟨⟨96,46,79⟩,mass_cell 23 96 46 79 109 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1273604417133, 141475139292, 418257046, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 23 :=
  ⟨⟨95,14,74⟩,mass_cell 23 95 14 74 155 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1101440855262, 287996332126, 22883758716, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 23 :=
  ⟨⟨85,25,76⟩,mass_cell 23 85 25 76 128 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1160303880874, 235812046684, 16616272912, 22429225, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 23 :=
  ⟨⟨105,45,79⟩,mass_cell 23 105 45 79 110 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1272669012284, 141417055202, 501799117, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 23 :=
  ⟨⟨96,18,75⟩,mass_cell 23 96 18 75 142 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1131138672842, 264483291536, 20064845399, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 23 :=
  ⟨⟨102,28,77⟩,mass_cell 23 102 28 77 124 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1197862519191, 207245830639, 8230472023, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 23 :=
  ⟨⟨90,37,78⟩,mass_cell 23 90 37 78 115 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1235819250568, 176186830899, 2973308157, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 23 :=
  ⟨⟨98,36,78⟩,mass_cell 23 98 36 78 116 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1235076270925, 176039492013, 3176577054, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 23 :=
  ⟨⟨112,44,79⟩,mass_cell 23 112 44 79 111 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1272721237444, 142359593345, 593197942, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 23 :=
  ⟨⟨105,35,78⟩,mass_cell 23 105 35 78 117 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1234963531641, 176305589745, 3311415439, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 23 :=
  ⟨⟨120,43,79⟩,mass_cell 23 120 43 79 111 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1272159671580, 142144332954, 650545127, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 23 :=
  ⟨⟨118,33,78⟩,mass_cell 23 118 33 78 119 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1235188200987, 176071598362, 3085793906, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 23 :=
  ⟨⟨118,12,75⟩,mass_cell 23 118 12 75 165 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1152496680810, 258702325374, 3577257482, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 23 :=
  ⟨⟨127,42,79⟩,mass_cell 23 127 42 79 112 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1272069763188, 142259445430, 684169433, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 23 :=
  ⟨⟨129,15,76⟩,mass_cell 23 129 15 76 153 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1182161446595, 229302457468, 1179958285, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 23 :=
  ⟨⟨120,6,74⟩,mass_cell 23 120 6 74 210 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1141175335434, 267435338604, 809335546, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 23 :=
  ⟨⟨130,8,75⟩,mass_cell 23 130 8 75 191 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1169046339785, 242379715014, 165093570, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 23 :=
  ⟨⟨122,24,77⟩,mass_cell 23 122 24 77 131 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1203123656849, 207205575095, 4335058752, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 23 :=
  ⟨⟨127,3,74⟩,mass_cell 23 127 3 74 256 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1159495808829, 253782434405, 55265490, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 23 :=
  ⟨⟨134,41,79⟩,mass_cell 23 134 41 79 113 (by decide)
    (by decide +kernel) [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1271910101498, 141916539001, 658618136, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 23) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55]

end Low6969Allocation.Group23
end Z6969Source2364

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles23
section Z6969Source2365
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group23
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19396037639, 36477280271, 87011181595, 61510293559, 43944330535, 35321049383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39330878759, 21849161091, 21781976523, 13158493643, 8762932703, 4451191263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099768517087, 1099600742919, 1099600743943, 43021705739, 4350524939, 72336907], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30120178191, 21530317327, 8645488143, 4350523919, 42971450903, 12906899991], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34364591643, 5227035], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 134 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32198629387, 53154560023, 87011519527, 18812420163, 35253939507, 30774497587], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34851434803, 43491408283, 34884838811, 13192049067, 8746156491, 1099852402123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852403147, 17436676575, 8846747103, 1099684626931, 1099684627955, 1099684628979], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4451185143, 4400855543, 43021638155, 21547092491, 38779411, 38780435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34364810779], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36561363983, 65720895515, 78404945971, 26546637115, 30573241659, 13477332283], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39498434899, 30841532755, 13192046007, 8863593911, 8762933687, 1099852402123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852403147, 1099751735779, 1099751736803, 1099751737827, 17319236087, 4367300091], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651071483, 8662197763, 4367299075, 25825210895, 17235349007, 1099567184399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4316898839, 4316966423, 22001175, 8595087899], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40688889875, 69915400227, 57047620663, 35270646083, 26563345731, 26328537411], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21832316251, 4769959259, 8830039475, 8729379251, 13192042955, 8813193675], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835624911, 1099835625935, 1099802067415, 1099802068439, 1099802069463, 1099701401071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701402095, 1099701403119, 43088818683, 21580578307, 12990715395, 4400851459], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [105886211, 4316898839], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40722709527, 78337631271, 35673452607, 31126676767, 26647299359, 26412491039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13175340411, 1100187946363, 1100187947387, 8947409339, 8796417467, 4501518779], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099885953475, 1099885954499, 1099885955523, 4417629679, 1099701401071, 1099701402095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701403119, 17352787443, 8762857971, 43038555655, 55553551, 55554575], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4333676051], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48926902299, 78287435819, 14332904519, 26781448471, 30690612503, 26261501207], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8880305551, 8796488079, 1100020174243, 1100020175267, 39112624559, 26227863983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13326259631, 8930633135, 4585337263, 1099885953475, 1099885954499, 1099885955523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099802065367, 1099802066391, 1099667845623, 1099667846647, 4384007683, 105885187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12957158923, 4300119579, 4300187163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53054231583, 73958983731, 1515114571, 30791272727, 26328606999, 13460555031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34968655243, 26328529291, 8930634143, 8796419487, 1100036948383, 1100020172195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100020173219, 1100020174243, 1099936289207, 13208819143, 4635665863, 1099818841555], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099818842579, 1099818843603, 172994035, 1099684622835, 21513468435, 12923605523], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4316897815, 5220891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61409419299, 56896625719, 22083968311, 17638012215, 9048148279, 35119653207], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22218114391, 4585403815, 1100003392935, 1100003393959, 1100003394983, 1100003396007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100003397031, 1100003398055, 8897076683, 4551780811, 4484739531, 1099701402095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651068411, 1099651069435, 17252124171, 8662194699, 72329739, 72330763], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34415141391, 21931543], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65570237479, 39817423935, 30975749435, 26412420411, 21932976443, 13192118615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100338942295, 1100020171171, 1100020172195, 1100020173219, 1100020174243, 8863525291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8762930603, 17436675543, 8796414423, 1099802064343, 1099802065367, 1099802066391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [189771247, 1099701400047, 4367229451, 72329739, 30086622743, 12906827287], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4316896791], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61292116011, 31311443007, 26613676355, 22083900739, 17654787395, 8880374123], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100255055211, 1100255056235, 1099953062323, 1099953063347, 1099953064371, 4585336247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4501517751, 1099936284087, 13158487511, 4568557015, 1099718178283, 1099718179307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [122662399, 1099634291199, 21530245647, 12940382735, 4300120603, 5220891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65436091439, 14249018439, 26630522147, 22117523747, 17654790435, 1100104060303], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100104061327, 8796486039, 1100070503831, 1100070504855, 8913854911, 4551781823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4484740543, 1099852398027, 1099852399051, 1099701401071, 1099701402095, 21630977523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8762858995, 122662399, 1099634291199, 55552527, 17185015323, 8595085851], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69613686833, 30774497547, 22050418955, 9199143179, 8863527319, 1100070501783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100070502807, 1100070503831, 1100036950431, 1100036951455, 1100036952479, 17554117047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8897078711, 1099785286107, 1099785287131, 1099785288155, 4400784899, 105885187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12923605523, 4333675027], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56846294069, 22151077163, 17671566635, 9064925483, 1100036950431, 1100036951455], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100036952479, 4568561059, 1100020170147, 1100020171171, 1100020172195, 8913853903], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4568558031, 4484739535, 1099734956519, 1099634291199, 1099634292223, 4333742611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 23 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group23
end Z6969Source2365

-- Source: ProximityPrize.SubmissionLower.Low6969Mass24
section Z6969Source2366
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group24

private def m0 : MassCell 24 :=
  ⟨⟨1,3,34⟩,mass_cell 24 1 3 34 216 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3179240176739, 2499283748733, 1890798175293, 1397816267757, 1005375586893, 699466035741, 467029859613, 295961646093, 175108325037, 94269168573, 44195791101, 16592149293, 4114542093, 371610717, 187906, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 24 :=
  ⟨⟨2,6,56⟩,mass_cell 24 2 6 56 192 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2152615884968, 1515778083380, 994996233092, 616051415252, 352670205476, 180729087860, 78254454980, 25422607892, 4559756132, 144372066, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 24 :=
  ⟨⟨1,9,65⟩,mass_cell 24 1 9 65 174 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1683640905688, 1038603744607, 579821019511, 284740614175, 114129109399, 31622429983, 3725844727, 15320781, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 24 :=
  ⟨⟨4,12,71⟩,mass_cell 24 4 12 71 161 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1772967741912, 1115049552348, 556754754972, 230385425052, 68394125532, 9763766364, 118509378, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 24 :=
  ⟨⟨1,14,73⟩,mass_cell 24 1 14 73 154 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1160730392788, 548252735828, 204121535188, 48043773268, 3486560468, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 24 :=
  ⟨⟨1,15,74⟩,mass_cell 24 1 15 74 151 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1187857981516, 543172593424, 190680860596, 39372152440, 1885424294, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 24 :=
  ⟨⟨1,18,76⟩,mass_cell 24 1 18 76 143 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1235811566114, 517695374608, 149518135312, 19022264080, 113153996, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 24 :=
  ⟨⟨1,19,77⟩,mass_cell 24 1 19 77 142 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1267633605937, 525202894425, 143959690225, 15860453025, 36117574, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 24 :=
  ⟨⟨1,21,78⟩,mass_cell 24 1 21 78 138 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1292337451466, 513966678456, 123072027852, 9131528136, 2638, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 24 :=
  ⟨⟨2,22,79⟩,mass_cell 24 2 22 79 136 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1323017001065, 528033966898, 120573319058, 7781872114, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 24 :=
  ⟨⟨5,24,80⟩,mass_cell 24 5 24 80 134 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1347339623525, 523233635135, 104052695963, 4389102535, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 24 :=
  ⟨⟨2,27,81⟩,mass_cell 24 2 27 81 130 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1371725336144, 521295568236, 85202301096, 1633197546, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 24 :=
  ⟨⟨6,30,82⟩,mass_cell 24 6 30 82 126 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1393552015086, 517550102718, 68051190174, 482648892, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 24 :=
  ⟨⟨1,35,83⟩,mass_cell 24 1 35 83 122 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1413489896853, 513227893206, 47085900258, 12596603, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 24 :=
  ⟨⟨3,40,84⟩,mass_cell 24 3 40 84 118 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429826106746, 516913085425, 32949967685, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 24 :=
  ⟨⟨1,48,85⟩,mass_cell 24 1 48 85 114 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 517166875125, 17783839278, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 24 :=
  ⟨⟨47,30,83⟩,mass_cell 24 47 30 83 127 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1412009311182, 507495235104, 58452597216, 503831016, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 24 :=
  ⟨⟨24,38,84⟩,mass_cell 24 24 38 84 120 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429520191116, 513668401582, 36495653614, 89636] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 24 :=
  ⟨⟨18,46,85⟩,mass_cell 24 18 46 85 115 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 519012554184, 20579262468, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 24 :=
  ⟨⟨52,35,84⟩,mass_cell 24 52 35 84 123 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429182520019, 509229014006, 40902041434, 32690034, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 24 :=
  ⟨⟨56,42,85⟩,mass_cell 24 56 42 85 118 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 515406908072, 24927591656, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 24 :=
  ⟨⟨52,25,82⟩,mass_cell 24 52 25 82 134 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1390645235254, 506354653951, 78004147559, 2515559937, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 24 :=
  ⟨⟨60,34,84⟩,mass_cell 24 60 34 84 124 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429118264273, 508499422012, 42149381980, 66552640, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 24 :=
  ⟨⟨68,33,84⟩,mass_cell 24 68 33 84 125 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429052722988, 507318327071, 42966352583, 111313437, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 24 :=
  ⟨⟨73,40,85⟩,mass_cell 24 73 40 85 119 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 513532739633, 26533853133, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 24 :=
  ⟨⟨67,19,81⟩,mass_cell 24 67 19 81 146 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1366902137537, 507737843815, 96086036063, 5731981382, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 24 :=
  ⟨⟨71,51,86⟩,mass_cell 24 71 51 86 113 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 527734819001, 12457663684, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 24 :=
  ⟨⟨69,27,83⟩,mass_cell 24 69 27 83 132 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1411665184580, 505599008906, 61608849806, 1058152287, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 24 :=
  ⟨⟨71,22,82⟩,mass_cell 24 71 22 82 139 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1390578608149, 506807767204, 79713861988, 3021140101, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 24 :=
  ⟨⟨75,32,84⟩,mass_cell 24 75 32 84 126 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429024656239, 507076538441, 43763802061, 162768702, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 24 :=
  ⟨⟨80,50,86⟩,mass_cell 24 80 50 86 114 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 526905103038, 12929595631, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 24 :=
  ⟨⟨86,19,82⟩,mass_cell 24 86 19 82 147 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1391306710160, 510564306933, 76191802333, 902708786, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 24 :=
  ⟨⟨87,24,83⟩,mass_cell 24 87 24 83 137 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1411728381681, 505904877747, 60596384679, 695461929, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 24 :=
  ⟨⟨82,31,84⟩,mass_cell 24 82 31 84 127 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1428995502785, 506420408335, 44026936479, 202382441, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 24 :=
  ⟨⟨88,49,86⟩,mass_cell 24 88 49 86 115 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 526606498337, 13416759293, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 24 :=
  ⟨⟨96,48,86⟩,mass_cell 24 96 48 86 115 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 526087271538, 13805345902, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 24 :=
  ⟨⟨88,14,81⟩,mass_cell 24 88 14 81 162 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1370197386009, 520487021584, 85991774232, 228650004, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 24 :=
  ⟨⟨104,47,86⟩,mass_cell 24 104 47 86 116 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 525336890940, 14069001578, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 24 :=
  ⟨⟨88,38,85⟩,mass_cell 24 88 38 85 121 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 512479227328, 27686322864, 1996292, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 24 :=
  ⟨⟨90,18,82⟩,mass_cell 24 90 18 82 149 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1391759768252, 513145767656, 74184656771, 326904980, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 24 :=
  ⟨⟨94,29,84⟩,mass_cell 24 94 29 84 130 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429012079979, 506865484926, 43935409906, 163078008, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 24 :=
  ⟨⟨102,36,85⟩,mass_cell 24 102 36 85 123 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 511290378746, 27877444082, 6683618, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 24 :=
  ⟨⟨111,46,86⟩,mass_cell 24 111 46 86 116 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 525185043172, 14337765955, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 24 :=
  ⟨⟨113,34,85⟩,mass_cell 24 113 34 85 125 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 512539261816, 27706351503, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 24 :=
  ⟨⟨117,45,86⟩,mass_cell 24 117 45 86 117 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 525684408062, 14632095394, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 24 :=
  ⟨⟨118,9,82⟩,mass_cell 24 118 9 82 191 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1397466732741, 539567832403, 42219057537, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 24 :=
  ⟨⟨118,3,81⟩,mass_cell 24 118 3 81 263 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1382798282998, 555208454478, 35713146462, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 24 :=
  ⟨⟨124,44,86⟩,mass_cell 24 124 44 86 118 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 525123705346, 14580056308, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 24 :=
  ⟨⟨119,33,85⟩,mass_cell 24 119 33 85 126 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 512138307203, 26737018787, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 24 :=
  ⟨⟨114,25,84⟩,mass_cell 24 114 25 84 136 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429192546760, 509869597819, 38769755828, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 24 :=
  ⟨⟨125,22,84⟩,mass_cell 24 125 22 84 141 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1429479930862, 515888789176, 33690021691, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 24 :=
  ⟨⟨124,32,85⟩,mass_cell 24 124 32 85 127 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 512752206904, 25874758180, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 24 :=
  ⟨⟨130,12,83⟩,mass_cell 24 130 12 83 173 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1415082467844, 531046349850, 30552696180, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 24 :=
  ⟨⟨128,31,85⟩,mass_cell 24 128 31 85 128 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 514472294591, 25252876804, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 24 :=
  ⟨⟨130,43,86⟩,mass_cell 24 130 43 86 118 (by decide)
    (by decide +kernel) [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 525238983319, 14524655119, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 24) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54]

end Low6969Allocation.Group24
end Z6969Source2366

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles24
section Z6969Source2367
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group24
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23473556487, 40638686223, 87028485151, 52971216955, 43860970799, 35204069679], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43475311919, 8964721043, 21815991727, 13192508847, 13108692399, 34532822503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4418094567, 47401021931, 1099651534319, 1099651535343, 30154193403, 17269365243], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8679503355, 4350984699, 8645881347, 1099550870023, 38677013003, 22462987], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22464011], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32232708107, 53155018775, 87011978279, 18796101699, 35220843827, 34986037555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30573704499, 43441535387, 34851743131, 13125399983, 4485203399, 1099819306439], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819307463, 21732102603, 13108619723, 4434868715, 4367761899, 1099617978871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099584422399, 1099584423423, 21530774019, 8645880323, 4350981635, 12907291147], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5684751], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40605131791, 65738198047, 74143992883, 30674292035, 26261957955, 9182824771], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39415074139, 30758106459, 8880762299, 8763324859, 4485203387, 1099768974803], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099768975827, 17403581911, 8796875223, 43139605987, 4401314279, 1099685085671], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099668309483, 1099668310507, 25825670659, 17235808771, 56014339, 56015363], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099567644163, 4317358603, 4317426187, 8595547663], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40756523027, 74160494627, 52786667579, 39498963255, 26614202679, 30573632823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17504255335, 1100221960551, 13242834355, 8863985075, 8763324851, 1099886413239], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099886414263, 1099886415287, 1099718638047, 1099718639071, 1099718640095, 4384468471], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [106345975, 38710565379, 21530771971, 12940843523, 42971902475, 4317358603], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5681679], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40739945495, 78354867239, 35673911359, 35271107875, 30791731491, 26345842979], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13125469563, 8897538479, 8780101039, 1099919966639, 1099886413239, 1099886414263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099886415287, 1099886416311, 21698546131, 8847204819, 4401313247, 1099718639071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4350914043, 89568763, 1099601197563, 34432378367, 42971905547, 17202252299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8612322827, 4317425163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48944138267, 86810720299, 5827316807, 31026542855, 30741403911, 26312292615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13091846539, 1100070963595, 13293164971, 8914315691, 8780101035, 43307387315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26161214899, 1099886415287, 1099886416311, 1099852857791, 1099852858815, 4401313243], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099735416283, 13024727535, 1099617973751, 1099617974775, 4384467451, 89567739], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42971908619, 4300579343], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57265771551, 73976220723, 26563874075, 30556924187, 9182759195, 39297635703], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26379320695, 13192505747, 8813656467, 1100037408147, 1099936745899, 1099936746923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936747947, 1099802524107, 1099802525131, 1099802526155, 13091838427, 4485130719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718570463, 1099718637023, 25792183819, 8595544591, 4300580367, 5680655], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57232351267, 61158430775, 22151469359, 21950214447, 9082095919, 35019514227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22117909875, 8830431651, 4535532963, 1099970299299, 1099953523111, 1099953524135], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099953525159, 8847203795, 4535462355, 1099718570463, 1099718637023, 1099718638047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718639071, 1099718640095, 21480441359, 5614095, 5680655], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65604250663, 39851437119, 30925876547, 22218575171, 17772684611, 13242841439], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8897612127, 1099936745899, 1099936746923, 1099936747947, 1099886344631, 1099886411191], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099886412215, 1099886413239, 8780096979, 4434801107, 17286139383, 8696209911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [106344951, 1099617973751, 55946755], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65553987627, 27050424387, 26664466747, 22151468347, 17722355003, 8847212919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100154850679, 1100154851703, 1099886412215, 1099886413239, 1099886414263, 4585795007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4468356543, 1099852856767, 13091837407, 8746542559, 1099668305387, 1099668306411], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4334134791, 39169543, 39236103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65470104623, 14283031623, 26630980907, 26329063723, 21849554219, 8813657479], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100020631959, 1100020632983, 1100020634007, 8981422515, 8830430643, 4485134771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852857791, 1099852858815, 1099701860835, 1099701861859, 4384468463, 1099651528175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21564327419, 8679431675, 39169543, 39236103], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65419841587, 1498796107, 26513543459, 22034099491, 13360284963, 1100020630935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100020631959, 1100020632983, 8863985067, 4518689195, 1099936743851, 1099903193523], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17420358103, 8796874199, 1099701860835, 1099701861859, 139833839, 139900399], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4317357579, 4317425163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56863464503, 22134693167, 21899883823, 4837526831, 8863987095, 1100020629911], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100020630935, 1100020631959, 1099903192499, 1099903193523, 13142171087, 4552240591], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4418090459, 1099735416283, 89568763, 1099601197563, 8595545615, 4300581391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [5681679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤52) :
    Covered orders a ∨ Low6969Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 24 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6969Allocation.Group24
end Z6969Source2367

-- Source: ProximityPrize.SubmissionLower.Low6969Mass25
section Z6969Source2368
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group25

private def m0 : MassCell 25 :=
  ⟨⟨1,3,42⟩,mass_cell 25 1 3 42 224 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2539267879198, 1921392628365, 1412737783293, 1010776340397, 699824465373, 465392530893, 294185116605, 174101009133, 94233202077, 44868896013, 17489498493, 4770624045, 582094173, 3752399, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 25 :=
  ⟨⟨1,6,63⟩,mass_cell 25 1 6 63 199 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1597576048746, 1057936578288, 662480435760, 385945937520, 203422014384, 92434160112, 32944431408, 7351447920, 490392240, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 25 :=
  ⟨⟨1,9,72⟩,mass_cell 25 1 9 72 181 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1694509171197, 1152806027516, 658288539872, 335979941228, 144457479584, 46287490940, 8025399296, 223551284, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 25 :=
  ⟨⟨1,12,77⟩,mass_cell 25 1 12 77 167 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1248419907198, 665243102295, 297013628547, 101282783823, 20048388795, 872258337, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 25 :=
  ⟨⟨4,14,80⟩,mass_cell 25 4 14 80 161 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1301057837455, 684846938098, 277987727506, 80087506994, 10732759762, 99043069, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 25 :=
  ⟨⟨5,15,81⟩,mass_cell 25 5 15 81 158 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1315828912752, 691290706072, 267465105364, 70298324680, 7424050036, 15978788, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 25 :=
  ⟨⟨1,18,83⟩,mass_cell 25 1 18 83 150 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1340641710296, 716035751708, 246742143548, 49112709980, 2101421406, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 25 :=
  ⟨⟨7,19,84⟩,mass_cell 25 7 19 84 149 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1348874087144, 727321492507, 234784476347, 41708706187, 1290185028, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 25 :=
  ⟨⟨6,21,85⟩,mass_cell 25 6 21 85 145 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 746540351223, 221827075287, 31781927679, 393668661, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 25 :=
  ⟨⟨1,24,86⟩,mass_cell 25 1 24 86 140 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 769613479677, 203612312241, 20290927365, 19362645, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 25 :=
  ⟨⟨5,26,87⟩,mass_cell 25 5 26 87 137 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 794742103900, 192847526760, 15062771688, 331998, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 25 :=
  ⟨⟨1,30,88⟩,mass_cell 25 1 30 88 132 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 817588063278, 172054713048, 7597688100, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 25 :=
  ⟨⟨10,33,89⟩,mass_cell 25 10 33 89 130 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 841251765748, 157404411168, 4474158180, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 25 :=
  ⟨⟨5,39,90⟩,mass_cell 25 5 39 90 125 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 865887498584, 135484560894, 1247470468, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 25 :=
  ⟨⟨9,46,91⟩,mass_cell 25 9 46 91 121 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 889250043064, 113170683652, 156824072, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 25 :=
  ⟨⟨37,30,89⟩,mass_cell 25 37 30 89 133 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 836221690368, 159712840056, 6906688580, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 25 :=
  ⟨⟨15,38,90⟩,mass_cell 25 15 38 90 126 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 864295203255, 136618113720, 1587391556, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 25 :=
  ⟨⟨66,26,89⟩,mass_cell 25 66 26 89 139 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 832742276932, 159574954086, 8895930806, 2403370, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 25 :=
  ⟨⟨50,34,90⟩,mass_cell 25 50 34 90 130 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 859568026825, 139594030342, 3197621500, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 25 :=
  ⟨⟨46,42,91⟩,mass_cell 25 46 42 91 124 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 885387016113, 116786592210, 589620711, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 25 :=
  ⟨⟨58,19,87⟩,mass_cell 25 58 19 87 152 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 784037821628, 193831548610, 22783308110, 305744133, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 25 :=
  ⟨⟨62,22,88⟩,mass_cell 25 62 22 88 145 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 808440352432, 177843465746, 15358195410, 66868491, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 25 :=
  ⟨⟨71,31,90⟩,mass_cell 25 71 31 90 133 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 858056326911, 140551103090, 4178688787, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 25 :=
  ⟨⟨70,39,91⟩,mass_cell 25 70 39 91 126 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 883315721304, 117981039375, 1044389025, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 25 :=
  ⟨⟨69,50,92⟩,mass_cell 25 69 50 92 120 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 908978091740, 93573037620, 38690283] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 25 :=
  ⟨⟨76,19,88⟩,mass_cell 25 76 19 88 153 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 811402377039, 178985951412, 12559525207, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 25 :=
  ⟨⟨77,24,89⟩,mass_cell 25 77 24 89 143 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 833133152622, 159488546371, 8369153722, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 25 :=
  ⟨⟨84,48,92⟩,mass_cell 25 84 48 92 121 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 908296053900, 94508585868, 85508760, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 25 :=
  ⟨⟨90,21,89⟩,mass_cell 25 90 21 89 149 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 836075531282, 159659356491, 5494887115, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 25 :=
  ⟨⟨91,47,92⟩,mass_cell 25 91 47 92 122 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 908054979813, 94879354574, 114299368, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 25 :=
  ⟨⟨77,38,91⟩,mass_cell 25 77 38 91 127 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 882941572004, 118276565628, 1186299468, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 25 :=
  ⟨⟨98,46,92⟩,mass_cell 25 98 46 92 122 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907775819185, 95010717262, 142410139, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 25 :=
  ⟨⟨105,45,92⟩,mass_cell 25 105 45 92 123 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907457904921, 94875260379, 164596937, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 25 :=
  ⟨⟨100,18,89⟩,mass_cell 25 100 18 89 156 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 841128403488, 159611547329, 2366456188, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 25 :=
  ⟨⟨88,28,90⟩,mass_cell 25 88 28 90 137 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 858309074701, 140641167436, 3984181275, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 25 :=
  ⟨⟨94,14,88⟩,mass_cell 25 94 14 88 169 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 820293513991, 175922850409, 3490198861, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 25 :=
  ⟨⟨102,25,90⟩,mass_cell 25 102 25 90 142 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 859926883328, 139399834785, 2168568689, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 25 :=
  ⟨⟨83,37,91⟩,mass_cell 25 83 37 91 128 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 882974416977, 118941033134, 1320748620, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 25 :=
  ⟨⟨101,34,91⟩,mass_cell 25 101 34 91 131 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 882747549210, 118610764448, 1290642253, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 25 :=
  ⟨⟨111,44,92⟩,mass_cell 25 111 44 92 124 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907433998872, 95025685739, 180418317, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 25 :=
  ⟨⟨109,15,89⟩,mass_cell 25 109 15 89 166 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 846615821332, 156083956355, 420715090, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 25 :=
  ⟨⟨107,9,88⟩,mass_cell 25 107 9 88 197 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 833409173963, 167200185454, 156167325, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 25 :=
  ⟨⟨115,31,91⟩,mass_cell 25 115 31 91 134 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 884049620612, 118281720033, 620684335, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 25 :=
  ⟨⟨117,43,92⟩,mass_cell 25 117 43 92 124 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907377528068, 94912896291, 177317634, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 25 :=
  ⟨⟨117,12,89⟩,mass_cell 25 117 12 89 179 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 852636362094, 150250056195, 16235000, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 25 :=
  ⟨⟨122,42,92⟩,mass_cell 25 122 42 92 125 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907628914733, 95156100082, 158663539, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 25 :=
  ⟨⟨127,41,92⟩,mass_cell 25 127 41 92 126 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 907854238246, 95149663048, 115364329, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 25 :=
  ⟨⟨116,21,90⟩,mass_cell 25 116 21 90 150 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 864614001368, 137123383958, 257857650, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 25 :=
  ⟨⟨123,29,91⟩,mass_cell 25 123 29 91 137 (by decide)
    (by decide +kernel) [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 885405141491, 117482188162, 173704370, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 25) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48]

end Low6969Allocation.Group25
end Z6969Source2368
