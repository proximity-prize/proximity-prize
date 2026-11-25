import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass13

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 1023479817, 10385626123, 23691141133, 82580158485, 87094102065], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765399629, 31309041921, 39865825537, 35520798977, 52247889153, 34799728977], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26243270061, 17636630957, 17485641133, 13090081213, 4516927933, 1099750361587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750362611, 1099750363635, 1099750364659, 1099733588471, 1099733589495, 8744777209], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4433035769, 34430476825, 12939010589, 8627335709, 54182429, 1099565811231], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [42986779169, 25807128097, 37404193, 34380144165, 4298813993, 4298816041], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15167657995, 32046655505, 86892169241, 69964635189, 39748520201, 39564243209], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43624470793, 26125911393, 17653406125, 13257780653, 13173964205, 8778337721], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985246651, 1099985247675, 30353682917, 17468854757, 1099783917035, 1099783918059], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783919083, 43204815341, 4416257525, 1099733583351, 1099733584375, 4432965129], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416255497, 34464028177, 1099599363607, 1099599364631, 8627267105, 3847721], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3848745], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27885708301, 65601749017, 86943039533, 10187560009, 30907269417, 34933874985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26293683497, 39664697653, 31058192693, 8845444521, 8761561513, 13291332021], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140341173, 8828666293, 1099918138827, 1099867804119, 1099867805143, 1099867806167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783917035, 1099750359539, 1099750360563, 1099750361587, 17401678325, 13056450037], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4483363317, 4416256501, 43087373833, 1099599362583, 1099599363607, 4365921817], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8627265057, 4332300833, 30085245477, 20624933, 34363363881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40368418833, 74141751329, 65569005625, 35302693169, 26696187185, 34900318513], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26142686541, 4818917709, 13090078121, 1100052352427, 1100052353451, 1100052354475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39178219949, 13341661621, 13173893557, 8811821493, 1099901360591, 1099901361615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834246623, 1099834247647, 1099767134703, 1099767135727, 1099767136751, 4466518525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416254461, 21579202065, 12989339153, 34447251989, 54178333, 1099565807135], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315522597, 3845673], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44630162453, 86859016229, 35672079425, 35319539981, 35068022029, 39145025805], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100236904831, 1100220128639, 13274558853, 13173965189, 8828670341, 39195065769], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30605272489, 17586228665, 13207445945, 1099951690179, 1099951691203, 1099901354447], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901355471, 1099901356495, 1099901357519, 4449743333, 1099800689127, 1099800690151], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17401677301, 4432962057, 4399409673, 121287181, 1099632915983, 8644041245], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315589157, 1099515551275], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57179719705, 82564186157, 14331531337, 30924046613, 34900320533, 26260129045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39446661469, 26595455325, 8862221709, 13324886425, 13157118361, 8845443481], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069130663, 1100069131687, 1100052355495, 1100018802087, 1099884580307, 1099851022811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851023835, 1099851024859, 4466520541, 1099834243551, 1099834244575, 13173820901], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8862146021, 4399409669, 1099649692171, 1099649693195, 38708660765, 37333537], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37400097, 1099532328483, 25790280229, 4298743337, 4298745385, 55848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57213473821, 86775335985, 35068022021, 30655754501, 13543067909, 35168540009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478082409, 8962814357, 8845376917, 1100136237463, 1100136238487, 1100069130663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069131687, 1100018801063, 1099985247655, 13324817841, 8979588529, 1099867798999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867800023, 1099867801047, 1099750289907, 1099750356467, 1099750357491, 4382631441], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [104508945, 21562423829, 12972560917, 56856, 4349075997, 56860], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55840, 56864, 55844, 56868, 3844649, 55848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846851617, 61156598841, 31108456753, 26612302129, 22149635377, 26193016113], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13341741361, 8878929305, 8811889049, 1100119461275, 1100085907875, 1100069131683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018801059, 1099968470435, 1099884577235, 1099884578259, 1099884579283, 8929254869], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4583958997, 4483297749, 1099817466339, 1099817467363, 17368121853, 13039670781], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666469383, 1099666470407, 56848, 56852, 56856, 54110749], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54177309, 55836, 56860, 55840, 56864, 8610485797], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55844, 56868, 4298744361, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69813365797, 48372428861, 31024639277, 26494864685, 26293676333, 17485645133], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100354345295, 1100304014671, 1100119459227, 1100119460251, 1100119461275, 1100119462299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069131675, 8929257901, 8795043245, 1100035572143, 13207375325, 8895700445], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817465315, 1099817466339, 1099817467363, 4399409665, 1099683246595, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56848, 25857388053, 17267526165, 56852, 55832, 56856], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54110749, 54177309, 55836, 56860, 54816, 55840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56864, 54820, 55844, 56868, 4298743337, 3778089], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69779879977, 35554638913, 26729675049, 26461377833, 26243346729, 13140413793], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203351395, 8912482717, 8778268061, 1100102683039, 1100085906851, 1100085907875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035577251, 1099985246627, 1099901353423, 1099901354447, 1099901355471, 13240997329], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8845370833, 1099767067119, 1099767133679, 1099767134703, 56840, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21579201041, 12989338129, 4399408657, 104508945, 56848, 55828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 55832, 56856, 55836, 56860, 54816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55840, 56864, 54820, 55844, 56868, 4298744361], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218888237, 14247645257, 30924047625, 30655685897, 26209797385, 8895776117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136239507, 1100085908883, 1100035578259, 1100002024851, 13274555801, 8878929305], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8795111833, 1099951689155, 1099901354447, 1099901355471, 1099901356495, 17519117785], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13157112281, 1099817465315, 1099817466339, 1099817467363, 4449741305, 1099716801019], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 56844, 55824, 56848, 55828, 56852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55832, 56856, 8644041245, 4349077021, 54812, 55836], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56860, 37400097, 54816, 55840, 56864, 54820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55844, 56868, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940766769, 5708044361, 30773055761, 30555091217, 13425627409, 13190672777], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8862220681, 1100186570123, 1100119462295, 1100069131671, 1099985246623, 1099934915999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13341594045, 8996364733, 8828595645, 1099901354447, 1099901355471, 1099901356495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867797975, 1099867798999, 4399410681, 1099716802043, 56836, 56840], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56844, 55824, 56848, 87731733, 1099599360535, 55828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 55832, 56856, 54812, 55836, 56860], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4332298785, 37333537, 54816, 55840, 56864, 54820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55844, 56868, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69645868085, 30689238293, 26226572565, 4886026517, 8878931333, 1100203346311], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203347335, 1100186571143, 1100136240519, 1099951692199, 1099901361575, 13308108205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912481709, 4567185837, 1099901354447, 1099901355471, 1099750357491, 1099750358515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [188329469, 188396029, 1099700024831, 56836, 56840, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55824, 56848, 8677596693, 4349078037, 55828, 56852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55832, 56856, 54812, 55836, 56860, 54816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55840, 56864, 4315589157, 54820, 55844, 56868], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group13
