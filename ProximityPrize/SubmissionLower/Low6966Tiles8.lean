import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass8

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 1040257033, 5670966283, 19211164685, 44495482897, 87026588705], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [48691130429, 35520254213, 39547329841, 39379764529, 43456703793, 43573851525], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4684700057, 17552747949, 13190676909, 13090017709, 26008389089, 17418527201], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433039841, 4416193017, 4382706169, 1099649702395, 1099649703419, 1099599368711], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599369735, 38725444105, 8660825609, 37407249, 37408273, 4298818073], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14596970505, 31945861137, 86875326489, 69947792437, 39782074629, 39564177669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43624405253, 21914830173, 1100303949151, 39144593829, 17636563369, 13291335081], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13173898665, 4466527689, 1099851027915, 1099851028939, 43238441429, 30303285729], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21679870433, 4416191985, 1099683186163, 1099683252723, 1099666476535, 1099666477559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644046349, 4332304909, 37339665, 34380213781, 21495386645, 8593713689], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3783193, 3784217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27684185101, 57162743833, 86926129193, 18710318149, 35185391905, 34967362849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30605426977, 39463371097, 35084724569, 13106790821, 13308042677, 13190671797], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845376949, 1099934847415, 1099934913975, 1099934914999, 1099934916023, 43221591513], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767073247, 1099767139807, 21646314985, 1099666406903, 1099666407927, 1099666408951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660823553, 104446465, 34430544393, 17200352789, 4315524629, 20559381], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36173983761, 82597336093, 61290751033, 35487175949, 35235723533, 43473411341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21830945105, 17636564365, 13291336077, 13157122445, 1099985179051, 1099985245611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985246635, 1099985247659, 43305480645, 1099817402835, 1099817403859, 1099817404883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817405907, 26008386017, 13123491297, 4449743345, 1099683183091, 1099683184115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8711153149, 3781145, 3782169], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40418950165, 86825329701, 39916648513, 31209055493, 30940759301, 34984207621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13190678897, 1100220062067, 1100203285875, 13257713053, 13157119389, 8795047325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43339038141, 1099901292991, 1099901359551, 1099817403859, 1099817404883, 1099817405907], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21746976217, 13106716121, 4449744353, 1099750292963, 1099750293987, 4432965113], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [70891017, 1099582519819, 8627265041, 4332300817, 30068468249, 1099515485723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57162876953, 86808756269, 10053276745, 30940758281, 34933809417, 26310460681], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39463438681, 30789759321, 8828601741, 1100102619535, 13324820885, 13190672789], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828600725, 1099985245611, 1099985246635, 1099985247659, 1099850960331, 1099817402835], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817403859, 1099817404883, 17401680349, 4466520545, 1099750291939, 1099750292963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660821505, 30135579145, 54112781, 1099565741583, 17200419349, 4315522581], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20557333], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61390935069, 82497081393, 35034468617, 30588581129, 9248036105, 35218806093], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26561902925, 13190673801, 8828601737, 1100119396747, 1099985245611, 1099985246635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951693227, 13341595053, 8962745773, 8862151085, 1099867735495, 1099867736519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867737543, 1099800624599, 1099800625623, 4382634481, 1099683183091, 4365854217], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332301833, 1099582518795, 25823836685, 20557333, 20558357, 56852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61391069217, 69696134197, 26394205473, 26209728801, 9130595617, 35134988625], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22267004241, 8912484749, 8795047309, 1100102619535, 1099985180071, 1099985246631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951693223, 13207379385, 8862150073, 1099884512707, 1099884513731, 1099884514755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767069151, 1099767070175, 1099767071199, 4382633469, 1099632850431, 8660819465], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365855241, 34413699597, 17217127953, 12922231313, 56848, 20558357], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 1099515483675, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69796523045, 48355586109, 31007796521, 26528419113, 26293610793, 17519199561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100320725323, 1100287171915, 1100035507615, 1100035508639, 1100035509663, 1100035510687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018734495, 8962812329, 8828597673, 1099985174955, 17418456545, 8828592609], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733513703, 1099733514727, 1099733515751, 4349079045, 1099532262919, 30118800909], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549039119, 56844, 56848, 20557333, 20558357, 56852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099515483675, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69763037225, 35571416129, 26763229477, 26461312293, 22015422757, 13140347237], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186507623, 1100152954215, 1100001954215, 1100001955239, 1100001956263, 1099968402855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8878928297, 4533632425, 1099985175979, 13207377357, 8878925261, 1099733515751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733516775, 4382634481, 1099683183091, 1099532262915, 70889993, 1099582518795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549039115, 56840, 56844, 56848, 25790282261, 4315522581], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20557333, 1099532260887, 55828, 56852, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73957409837, 18492214341, 26696123665, 26427760913, 26226507025, 8912485761], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795048321, 1100119397763, 1100069067139, 1100069133699, 9013076401, 8895704497], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4550408625, 1099934845367, 1099934846391, 1099934847415, 1099817402835, 1099817403859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21646312945, 13022895601, 1099683183091, 1099683184115, 4382633469, 1099632850431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549039115, 56840, 56844, 56848, 8610487829, 20557333], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20558357, 1099532260887, 55828, 56852, 4298746393, 55832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73923924017, 5691201609, 30806610189, 30555025677, 13425561869, 13224227205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845377925, 1100136172935, 1100085842323, 1100052288915, 1100002023835, 1099968470427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535898049, 8929256897, 1099867734471, 1099867735495, 1099867736519, 4483297753], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783846363, 1099783847387, 70889993, 1099582518795, 56840, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55824, 56848, 4315522581, 20557333, 1099532260887, 55828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 17183642137, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69629025333, 26478091537, 22032202001, 13408784657, 1100085842323, 1100052288915], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035578259, 1100002024851, 8862153113, 1100052284827, 1100052285851, 1100052286875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207379389, 8845372861, 1099767069151, 1099767070175, 1099767071199, 4399410685], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099632850431, 56840, 8644042253, 4349078029, 56844, 55824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56848, 1099532260887, 55828, 56852, 3781145, 55832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56861632569, 22048975153, 21864497457, 4751743281, 8811823505, 1100085841299], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085842323, 1100052288915, 1099985246627, 1099934916003, 8912480701, 4567184829], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901287871, 1099850957259, 1099850958283, 1099850959307, 1099616073219, 1099616074243], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56840, 4349078029, 54112781, 56844, 56848, 1099532260887], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55828, 56852, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group8
