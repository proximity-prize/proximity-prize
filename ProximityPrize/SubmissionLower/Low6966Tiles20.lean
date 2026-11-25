import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass20

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10922626053, 28020316171, 49009865751, 87094748199, 27435251779, 35320390983], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35085650247, 39145811271, 43440420287, 34850628031, 17486425535, 8829452755], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4517711315, 21730986487, 13141123575, 4467307019, 4450597387, 1099684040203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099684041227, 4366713359, 1099667261967, 1099583373859, 1099583374883, 43004205607], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21496104495, 4635187, 4636211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27986761739, 48942756887, 86994084903, 27334588483, 35337168175, 30857726255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34934729007, 43473974703, 30622769583, 13225011643, 13090798011, 8779123131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099818256875, 1099818257899, 1099818258923, 17469573615, 13124345327, 4433754607], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801477615, 1099801478639, 4416974351, 1099667191311, 1099650480659, 1099650481683], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21579989531, 38742792733, 8628051499, 4333087275, 38675825197, 21344815], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36409648143, 78403880985, 65603343413, 35504736547, 31075757347, 30841015587], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26210577747, 9097824595, 8896490943, 8779053503, 1100002805183, 1099935697359], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935698383, 1099935699407, 17469574623, 8896487903, 1099801410031, 1099801476591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801477615, 43188758011, 172338699, 1099683967499, 1099683968523, 25891663383], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17285024279, 8644828711, 38119979, 12889393713, 8594496051], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36561039379, 74159379485, 57030188085, 35353810227, 26696972595, 26428609843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17654198615, 13275350357, 1100036359607, 1100036360631, 1100036361655, 1100036362679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4534415819, 1099952404939, 1099952405963, 1099952472523, 8997082579, 8879710675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4551192019, 1099700745735, 21613541907, 13006901779, 1099650412051, 1099650413075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4400194075, 105228827, 43021054499, 30136294945, 8594494001], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48909335573, 82598456357, 22922247233, 26915007767, 30790617365, 30589364501], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13191457173, 8829385109, 1100137022879, 1100137023903, 1100137024927, 1100137025951], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39246118311, 26361357733, 13342378439, 9013926343, 8846157255, 1099918850515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918851539, 1099918918099, 1099851739619, 1099851740643, 4400195079, 1099700743687], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71673377, 1099583302179, 17217913387, 4316305965, 21340717], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53087062041, 86809672749, 1564856393, 30941609225, 34917883145, 17788420361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39296518543, 26378203535, 13292051857, 13157903761, 1100187286931, 1100136956319], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100137022879, 1100137023903, 1100137024927, 1099986031043, 1099902070231, 1099902071255], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099902072279, 1099902073303, 13191384543, 4551187959, 4433749495, 105227803], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616856603, 21546431009, 12956502563, 34397637161, 25807842859, 4333083177], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61459026973, 69730537521, 30656467237, 26227355941, 4869967141, 35202880863], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22301342047, 8879714709, 1100170509719, 1100170510743, 1100170511767, 1100170578327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100053138867, 1100053139891, 13292048823, 8930042293, 4584746421, 1099868517855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099868518879, 1099734298111, 1099734299135, 4383416841, 1099683965451, 8695157273], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4383415833, 1099583301155, 17234688549, 8644824613, 34397705771, 4562481], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4563505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69847703585, 48406766649, 31092465971, 26545979697, 26294394161, 13292124497], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8930052433, 1100103469479, 1100103470503, 1100103471527, 8997150129, 8846158257], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100053067187, 1100036290999, 1100036292023, 1100036293047, 1100036359607, 17469571567], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8862930413, 1099784628723, 1099784629747, 1099784630771, 122003989, 1099633632791], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30102741545, 4299527729, 4562481], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69814217765, 35605753917, 26831121711, 26478872877, 22016206125, 13141130601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100355128683, 1100355129707, 1100086623659, 1100086624683, 1100086691243, 1100086692267], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8896488881, 1100053066163, 1100053067187, 1100053068211, 13258492377, 8896485849], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099734296063, 1099734297087, 1099734298111, 4349860389, 54895141, 25791065645], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78253226025, 14298760261, 30991939853, 30690023693, 26227357965, 8879716733], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153800091, 1100153801115, 1100153802139, 1100153803163, 13258496421, 8896489893], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100103398823, 1099969182151, 1099969183175, 1099969249735, 21764536813, 8879641069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784628723, 1099784629747, 1099784630771, 4500856321, 205891073], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82464375853, 30924834045, 30656472317, 13527008509, 13241787789, 8862938509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100204065167, 1100153800091, 1100153801115, 1100153802139, 1100153803163, 17570235853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8963594701, 1099918849491, 1099918850515, 1099918851539, 4500858341, 1099834961383], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834962407, 105227801, 1099616856603, 4333083177, 38117929, 12906169901], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8611272237], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69680205873, 26529272089, 26277686553, 9148156185, 8930045333, 1100170508695], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100170509719, 1100170510743, 1100170511767, 1100120246691, 1100120247715, 1100120248739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13208162769, 8829379025, 1099818184171, 1099818185195, 1099818186219, 4400194061], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099667188239, 8661602849, 4366638625, 38118953], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56895970357, 22083312949, 17654199605, 9030715701, 1100120246691, 1100120247715], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100120248739, 1100086621611, 1100086622635, 1100086623659, 1100086624683, 1100086691243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8930041289, 4584745417, 1099952402891, 1099650411027, 1099650412051, 4383415837], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [88450589], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 20 where
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
end Low6966Allocation.Group20
