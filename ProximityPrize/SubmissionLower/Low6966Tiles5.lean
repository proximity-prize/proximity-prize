import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass5
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1040257033, 4613805065, 22901955597, 57044841493, 87026592805], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31578243137, 19110564953, 31275421957, 31007665461, 39262194997, 43372688693], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39647655225, 35269008697, 39463170405, 17468667293, 13089884589, 1100018604463], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018605487, 21813956041, 13190473161, 1099800496611, 1099800497635, 1099800498659], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099800499683, 8761357797, 4432839141, 1099632722443, 1099632723467, 4348950033], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099599166995, 34430344725, 8660690453, 4365726229, 21528740377, 12922034717], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [20429345], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10318583819, 27482661901, 78251507737, 86959688753, 35604283645, 35403228413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47885617405, 34799532337, 1100538699059, 17770580377, 21830737305, 13207254425], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106660765, 8778143133, 39177951657, 1099884385743, 1099884386767, 1099850827223], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850828247, 1099850829271, 1099850830295, 4466390505, 1099766939115, 1099766940139], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8811617777, 4516653553, 4466389489, 30252819961, 21646181881, 1099582388759], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37204509, 37205533, 17183442469], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27482661901, 52867579929, 82647807017, 27182679109, 30907004197, 30722594085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34816308517, 39446462809, 26628811097, 13173699989, 8845247897, 1100102488475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102489499, 1100085713307, 1100052159899, 39178020265, 13257577925, 8895505861], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8778068421, 1099834050011, 1099834051035, 1099834052059, 1099817270751, 1099817271775], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17401546225, 4399280629, 1099716606455, 4382500369, 87535121, 87536145], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099599164947, 34413497881, 1099532131871, 8610290209, 1099515353639, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36073189393, 69812900893, 74058078261, 31141745957, 26695922981, 30705815845], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26259927345, 17653288241, 1100052155815, 1100052156839, 1100018603431, 1099985050023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951496615, 8861954473, 8794914217, 1100035377579, 39161311661, 13291131329], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8912282049, 8794844609, 1099817270751, 1099817271775, 1099817272799, 1099750160879], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4399279605, 1099716605431, 21612557829, 13022694917, 4382433809, 87534097], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [87535121, 1099599163923, 1099532131859, 1099532130843, 56856, 56860], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532129827, 55840, 56864, 4298546725, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44478905365, 78285596709, 44161152061, 26880403729, 35034268945, 30605158673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17435183457, 1100186377571, 39295466885, 26444260741, 13190474133, 8828402069], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119262615, 1100068932003, 1100068933027, 1100035379619, 1099985048995, 1099951495587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17619584437, 9046497717, 8895505845, 1099867601363, 1099867602387, 1099867603411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099800490467, 1099800491491, 4382434817, 1099666271747, 1099532131847, 1099548908047], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56844, 56848, 1099548907031, 56852, 4332168729, 55832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56856, 17216995869, 55836, 56860, 38674906657, 8610289185], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532128803, 54816, 55840, 56864, 4298613285, 3648037], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48723806233, 82513590313, 22803826757, 30940559621, 34950453509, 34782756101], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13173701997, 35067677053, 26444328317, 1100152819079, 1100102488455, 1100068935047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035381639, 1100001828231, 13341464981, 13173696917, 8811624853, 1099985044919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099985045943, 1099884378575, 1099884379599, 1099884380623, 13207243225, 4466321885], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817267679, 1099817268703, 1099532131839, 8694176261, 4399277573, 1099532130823], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56836, 1099632717323, 56840, 1099548907023, 55820, 56844], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55824, 56848, 53780, 55828, 56852, 53784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54808, 55832, 56856, 53788, 54812, 55836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56860, 25790082593, 4315322913, 4315390497, 20425249, 52768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 52772, 53796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61306852381, 82463395889, 30756081921, 34833084673, 9231127809, 31057859897], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26578482489, 13207253365, 8895578485, 1100186373495, 1100152820087, 1099934717343], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901163935, 1099867610527, 13307842985, 8962613673, 8828399017, 1099934712259], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934713283, 1099917937091, 1099917932999, 1099917934023, 1099783712231, 1099783713255], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783714279, 1099532131831, 21646112253, 13056249341, 1099548908031, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56832, 4399211013, 137865733, 54788, 56836, 54792], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55816, 56840, 1099515352591, 55820, 56844, 4382432785], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 53780, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56856, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [20424225, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61306986529, 69645671477, 30605155605, 30420679957, 1100404481303, 30957265213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22283583805, 22048774461, 8912289133, 8845248877, 1100119266671, 1100085713263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845177241, 1099985045935, 1099934715311, 1099901161903, 1099951488447, 1099951489471], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951490495, 8929057225, 4583761353, 4483100105, 1099834045915, 1099834046939], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548909039, 1099699826171, 1099699827195, 1099532130811, 56824, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17334436353, 8744506881, 54784, 55808, 56832, 54788], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55812, 56836, 54792, 55816, 56840, 53772], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54796, 55820, 56844, 87533073, 87534097, 53776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 56848, 30135378453, 52756, 53780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54804, 55828, 56852, 52760, 53784, 54808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55832, 56856, 4332167709, 52764, 53788, 54812], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55836, 56860, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55840, 56864, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65518201893, 52566535229, 26763029805, 26444335405, 21998445869, 17569332533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13224104245, 1100035379595, 1099985048971, 1099951495563, 1099901164939, 1100119260567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119261591, 1100119262615, 1100068931991, 1100035378583, 8895505837, 4550209965], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018596271, 13240732113, 8912280017, 1099548909035, 1099750158831, 1099750159855], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532130807, 56820, 188130809, 188197369, 1099699826171, 56824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54780, 55804, 56828, 54784, 55808, 56832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54788, 55812, 56836, 53768, 54792, 55816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56840, 53772, 54796, 55820, 56844, 53776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 56848, 52756, 53780, 54804], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55828, 56852, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56856, 25806859805, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55836, 56860, 4315322913, 4315390497, 51744, 52768], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 51748, 52772], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53796, 54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [73957210153, 31225921601, 26746255629, 26494735629, 26276704525, 13089885529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085714267, 8895508873, 8811691401, 1100119263627, 1100052155791, 1100001825167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968271759, 1099917941135, 13224023485, 8828396989, 1099934711235, 1099934712259], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934713283, 1099850822103, 1099850823127, 1099850824151, 1099548909031, 55792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56816, 1099532130807, 56820, 21662890489, 13039473145, 4399212025], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099699826171, 56824, 54780, 55804, 56828, 54784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 56832, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 53772, 54796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55820, 56844, 4348879377, 52752, 53776, 54800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55824, 56848, 70756885, 52756, 53780, 54804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55828, 56852, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56856, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56860, 8610288161, 4315323937, 20424225, 51744, 52768], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 51748, 52772], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53796, 54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69679088685, 22703163461, 30789633301, 26310190357, 21897855253, 1100052158831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100001828207, 8828469629, 1100119264639, 1100068934015, 1100018603391, 8979391897], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828400025, 1100102483355, 1099968266683, 1099968267707, 1099917937083, 17569252805], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8962611653, 1099850822103, 1099850823127, 1099850824151, 1099548909031, 55792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56816, 1099515353591, 56820, 4399212025, 1099699826171, 54776], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55800, 56824, 54780, 55804, 56828, 54784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 56832, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 53772, 54796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55820, 56844, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 4332168725, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56852, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4315322913, 4315390497, 20425249, 51744, 52768, 53792], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54816, 55840, 56864, 17183442469, 51748, 52772], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53796, 54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82379509809, 35051049197, 30605227245, 9247905005, 13173699953, 1100270257523], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100219926899, 1100169596275, 1100119265651, 1099951494543, 1099901163919, 1099867610511], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13425283477, 13240803733, 8861954453, 1099968265659, 1099968266683, 1099834044891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834045915, 1099834046939, 1099532131815, 4516651501, 1099750091247, 1099750157807], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55788, 56812, 55792, 56816, 1099515353591, 56820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54776, 55800, 56824, 54780, 55804, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54784, 55808, 56832, 53764, 54788, 55812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56836, 53768, 54792, 55816, 56840, 53772], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 52752, 53776, 54800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55824, 56848, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56852, 8643842585, 4348878361, 52760, 53784, 54808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55832, 56856, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55836, 56860, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55840, 56864, 3647013, 51748, 52772, 53796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69595339829, 30655487241, 26192821513, 4869052681, 8878734705, 1100219926899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169596275, 1100119265651, 1100068935027, 1099867609495, 1099817278871, 13291134361], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895507865, 8794913177, 1099968267707, 1099884378575, 1099884379599, 1099884380623], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099548909027, 4432834021, 1099783714279, 55788, 56812, 55792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56816, 1099515353591, 56820, 54776, 55800, 56824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4466318845, 4399212029, 54780, 55804, 56828, 54784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 56832, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099632717323, 1099632718347, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 52752, 53776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54800, 55824, 56848, 52756, 53780, 54804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55828, 56852, 4332168729, 52760, 53784, 54808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55832, 56856, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55836, 56860, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55840, 56864, 3647013, 3648037, 51748, 52772], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53796, 54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56777549881, 22032001309, 17636442397, 9046578461, 1100152816015, 1100152817039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102486415, 1100052155791, 1100001825167, 1099951494543, 1099901163919, 1099850833295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895506853, 8761292197, 1099867600339, 1099867601363, 1099867602387, 1099548909027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55788, 56812, 221686257, 204975601, 137867761, 55792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56816, 1099515353591, 56820, 54776, 55800, 56824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54780, 55804, 56828, 54784, 55808, 56832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 53768, 54792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55816, 56840, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 45588], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 45592], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 45596], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [45600, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56864, 44580, 45604, 51748, 52772, 53796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54820, 55844, 56868], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group5
