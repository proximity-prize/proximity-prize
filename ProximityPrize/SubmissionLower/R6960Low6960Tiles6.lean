import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
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
  ⟨unpack [2248215557, 1006702601, 4949414921, 18959375373, 56994443281, 86993037349], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [40084356161, 31577019561, 31275421949, 39664432425, 35302563113, 35101442349], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39178380589, 17384918425, 1100069003675, 17519060397, 17384847789, 1099850894799], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850895823, 1099850896847, 1099850897871, 1099850898895, 21730066913, 17384839649], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4483168737, 4449681889, 1099767007715, 4416056833, 4416124417, 1099599233547], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099599234571, 34430344717, 54050321, 42986648085, 12922100245, 4332169749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 135 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10469644299, 27516281869, 78251573273, 86942911537, 1597497421, 35570794749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35352896765, 43641047293, 34833151277, 9214417197, 13156988321, 8828470689], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778207649, 21897841061, 17519059365, 39110976945, 1099884453319, 38993533389], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850899919, 1099834118611, 1099834119635, 1099834120659, 1099783783903, 1099783784927], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783785951, 4432836069, 1099750227431, 1099750228455, 30269597165, 21646181869], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8744575481, 4432834041, 87602697, 1099599231499, 8660688397, 21495252505], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3649053, 3715613], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27516281869, 52867645465, 86875665449, 27132348485, 30957401365, 34967229717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43355978005, 35185049945, 30839956825, 17468733817, 13073173901, 1100102557071], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069003663, 13324686761, 13207315881, 8845243817, 39110976945, 1099918003647], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918004671, 1099918005695, 1099918006719, 1099901223363, 1099901224387, 1099901225411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733382635, 1099733383659, 1099733450219, 17384769005, 4449609209, 4382502393], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53980689, 1099565609491, 30101890581, 8627132949, 57876, 57880], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i49 : checks (tilesOf batches) 135 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40200450065, 86791575585, 56945388605, 31242410233, 39413119225, 39245488377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21780482377, 1100303884619, 39295529349, 17518993801, 13156988297, 8828470665], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085776791, 1100085777815, 1100052224407, 1100018670999, 21914548657, 13307908529], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884447175, 1099884448199, 1099884449223, 1099850823119, 1099850824143, 1099850825167], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850891727, 8794907101, 4466388445, 1099599162891, 1099599163915, 57864], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57868, 4348944913, 53979665, 56848, 57872, 30101821973], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56852, 57876, 12905320985, 55832, 56856, 57880], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [21478406685, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i52 : checks (tilesOf batches) 135 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44478970901, 82530297893, 44110886977, 31074773253, 30840031493, 34883414277], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17401630041, 1100186444123, 39295532421, 26410771845, 13257648517, 13123434885], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100152818055, 1100102552979, 1100102554003, 1100052223379, 1100018669971, 1099985116563], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17502210497, 8929123777, 1099901155779, 1099901156803, 1099901223363, 1099901224387], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466387425, 1099766936035, 1099766937059, 17334436345, 57852, 57856], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56836, 57860, 56840, 57864, 70756877, 1099582385679], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55820, 56844, 57868, 8643909137, 55824, 56848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57872, 4332167701, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 54812, 55836], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52867778585, 86741515309, 18492149833, 30940626169, 34933677305, 34799599865], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185117529, 26544991577, 13156991333, 13324688773, 13190540677, 8828468613], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119331207, 1100069000583, 1100035447175, 1100001893767, 1099968340359, 1100001888683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001889707, 1099901156803, 1099901223363, 1099901224387, 13224020429, 8912345549], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466388433, 1099834045907, 1099834046931, 4416054769, 57844, 57848], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099649494527, 1099649495551, 56828, 57852, 56832, 57856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55812, 56836, 57860, 55816, 56840, 57864], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 53978641, 53979665], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 25806925333, 54804], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55828, 56852, 57876, 53784, 54808, 55832], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56856, 57880, 4298611229, 4298613277, 53788, 54812], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61306917917, 86724874289, 30789701881, 34833084665, 13458986233, 35218675001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22367467833, 13240873325, 13106659693, 1100186440047, 1100052223367, 1100001892743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968339335, 1099934785927, 1100018598311, 1100018599335, 1100018665895, 1100001889703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13307908521, 8962679209, 8811687337, 1099884378567, 1099884379591, 1099766935011], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099766936035, 1099766937059, 57836, 57840, 56820, 57844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56824, 57848, 55804, 56828, 57852, 55808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56832, 57856, 4382499333, 1099615939079, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57860, 34447119881, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 21528738321, 8643908113], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4348943889, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 53784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 3647005, 52764], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61307052065, 73873529909, 30655552773, 26243218693, 9113688325, 30957330749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22283649341, 22048839997, 8845245817, 1100169595259, 1100169661819, 1100119331195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069000571, 1099985115527, 1099951562119, 1099901231495, 8845242773, 1099934711227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934712251, 1099934778811, 8929122761, 4583826889, 4483165641, 1099817268695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817269719, 57828, 57832, 57836, 56816, 57840], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56820, 57844, 1099666271739, 1099666272763, 55800, 56824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57848, 55804, 56828, 57852, 17300881921, 8711017985], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 54788, 55812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56836, 57860, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 53978641], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099565607443, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [30101889557, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532126747, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57880, 3645981, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 135 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [73957141541, 48288412733, 31024442633, 26545065225, 26327034121, 21730149689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100253551931, 1100203221307, 1100203148667, 1100152818043, 1100152884603, 1100102553979], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052223355, 1100018669947, 13156985233, 8778135953, 1099901155779, 1099901156803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901223363, 13257575877, 8895569349, 4483164629, 1099817267671, 1099817268695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57824, 57828, 57832, 56812, 57836, 25957920241], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13073025521, 56816, 57840, 55796, 56820, 57844], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55800, 56824, 57848, 54780, 55804, 56828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57852, 54784, 55808, 56832, 57856, 1099615939079], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099615940103, 54788, 55812, 56836, 57860, 53768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 53772, 54796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55820, 56844, 57868, 4348943889, 53978641, 53776], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 1099548903959, 52756], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 52760], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 52764], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69712640041, 39732034625, 26679212313, 26394072345, 26192818457, 13140217157], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186443079, 1100136112455, 13140210049, 1100169593219, 1100169594243, 1100119263619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085775751, 1100052222343, 1100001891719, 1099951561095, 9046496689, 8929124785], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4583828913, 1099901154755, 1099901155779, 1099901156803, 57820, 57824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57828, 56808, 57832, 56812, 57836, 55792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 57840, 21646178805, 13039538677, 55796, 56820], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57844, 1099666271739, 1099666272763, 55800, 56824, 57848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 54784, 55808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56832, 57856, 4382499333, 1099615939079, 54788, 55812], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56836, 57860, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57864, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532126743, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57876, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57880, 8593576477, 3645981, 3647005, 51740, 52764], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82413061165, 14130074697, 35101377777, 30638778609, 26209667313, 8845248861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052223351, 1100018669943, 1099968339319, 1099934785911, 13240871293, 8862022013], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100169594239, 1100035443103, 1099985112479, 1099934781855, 17686758821, 9046497701], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8929125797, 1099901155779, 1099901156803, 1099901223363, 1099817267671, 1099817268695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57820, 57824, 56804, 57828, 56808, 57832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 57836, 55792, 56816, 57840, 55796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56820, 57844, 4382500345, 1099666271739, 54776, 55800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56824, 57848, 54780, 55804, 56828, 57852], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 53764, 54788], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55812, 56836, 57860, 53768, 54792, 55816], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56840, 57864, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57868, 53978641, 53979665, 52752, 53776, 54800], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55824, 56848, 57872, 8627132949, 52756, 53780], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 52760, 53784], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 1099515348511, 51740], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82379575345, 1312284749, 30840033517, 30588449005, 17703620845, 13224096109], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845246829, 1100136041839, 1100136108399, 1100085777775, 1100052224367, 1100001893743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099850899851, 13341462953, 8979456425, 8811687337, 1099985043887, 1099985110447], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968334255, 1099901155779, 1099901156803, 57820, 1099766935011, 1099766936035], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099766937059, 57824, 56804, 57828, 56808, 57832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 57836, 55792, 56816, 57840, 55796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56820, 57844, 54776, 55800, 56824, 57848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 54784, 55808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56832, 57856, 1099548904967, 53764, 54788, 55812], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56836, 57860, 4382499337, 87534089, 53768, 54792], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55816, 56840, 57864, 53772, 54796, 55820], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56844, 57868, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56848, 57872, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56852, 57876, 12905320985, 52760, 53784, 54808], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55832, 56856, 57880, 51740, 52764, 53788], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69561785397, 1312284749, 30672329985, 26226441473, 9080133889, 8878800241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186372467, 1100169661811, 1100119331187, 1100069000563, 1100001892731, 1099951562107], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834122635, 13257579925, 8912350613, 1100085705111, 1099934711227, 1099934712251], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934778811, 57816, 57820, 57824, 1099750157799, 1099750158823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750159847, 56804, 57828, 56808, 57832, 56812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57836, 8744574449, 188197361, 55792, 56816, 57840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55796, 56820, 57844, 54776, 55800, 56824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57848, 54780, 55804, 56828, 57852, 54784], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55808, 56832, 57856, 53764, 54788, 55812], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56836, 57860, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57864, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532126743, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57876, 4315389465, 20424217, 52760, 53784, 54808], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55832, 56856, 57880, 51740, 52764, 53788], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54812, 55836, 56860, 57884], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((6 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 6+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group6
