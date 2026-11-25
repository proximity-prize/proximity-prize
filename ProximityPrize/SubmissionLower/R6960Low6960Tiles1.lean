import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass1

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1006702601, 4597027849, 22683720717, 48572281877, 129657365541], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14832112725, 39597401321, 60686568681, 22300444905, 31292002557, 35386110257], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30940419413, 22048705905, 21914559857, 9096838513, 8744520113, 1100001760691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001761715, 1100001828275, 21847373261, 1099833985499, 1099833986523, 1099833987547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8794777053, 4516655581, 1099817204191, 1099750096367, 1099750097391, 1099750098415], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13056183805, 8744443389, 4365658641, 70693397, 1099582322199, 30067986981], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8593514021, 20359716], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9882245131, 23321846797, 52817116181, 116772532265, 39480029421, 52096702701], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17971989741, 35318864193, 35285581129, 26695786825, 17669855605, 17552485749], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979399029, 1100018535855, 1100018536879, 1099984983471, 1099951430063, 1099968273839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17653071285, 13307842997, 8761290193, 1099867535827, 1099867536851, 1099850760663], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850761687, 1099850762711, 4516585965, 4466321901, 1099682984447, 1099682985471], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [53914137, 1099565542939, 1099532065307, 8626999837, 4332035613, 56860], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532064291, 16833056, 3581476, 16833060], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23321846797, 44394953749, 108165818405, 14297714761, 35336055013, 43607362789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22250109157, 35117874545, 26528080241, 17669852549, 17518928261, 8912221573], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018536863, 1099984983455, 1099951430047, 1099951496607, 1100068864419, 1100068865443], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100068866467, 1100035313059, 21863867849, 17535630801, 1099850757591, 1099850758615], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850759639, 4550140377, 4466256345, 1099833979355, 8761217533, 4449476093], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099649427975, 1099649428999, 1099532065291, 56840, 56844, 1099532064275], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833040, 16833044, 53913113, 1099532063259, 33609240, 33609244], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532062243, 50385440, 4298546725, 50385444], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [31862042641, 57078927389, 91053262897, 35017427201, 30638714113, 17770663169], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30957130057, 22317003081, 8912219533, 8845179277, 1100135974287, 1100102420879], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052090259, 1100001759635, 1099968206227, 1099934652819, 1099901099411, 13374884257], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13223958945, 1100068792739, 34782327233, 1099884313039, 1099884314063, 1099884315087], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817201119, 1099817202143, 1099817203167, 1099548843507, 4499806709, 4399145461], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548842491, 56828, 1099548841475, 56832, 16833028, 1099548840459], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833032, 33609228, 87466513, 87467537, 33609232, 21545382421], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099532062231, 50385428, 8643775001, 53843481, 50385432, 83937820], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [25789945377, 83937824, 100714020], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44378176533, 69762770981, 52616801341, 26695788833, 30672127265, 22048777505], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21763571009, 8929072449, 35134586221, 26528080237, 1100169526667, 1100169527691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119197067, 1100068866443, 1100035313035, 1100001759627, 1099901097367, 1099867543959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099833990551, 8828331437, 1100018528687, 1100018529711, 1100018530735, 13324551605], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8979322293, 4650803637, 1099548843495, 1099766868459, 1099766869483, 1099548842479], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 1099548841463, 56820, 16833016, 16833020, 13039336961], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532063235, 33609216, 33609220, 67161608, 104243725, 1099615872527], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [3657228, 50385420, 83937808, 4365587989, 70622741, 83937812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [83937816, 100714012, 4315254305, 100714016, 25773236773, 100714020], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52817381401, 82463259693, 18458463301, 30839831805, 30655421693, 13542735101], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35168209229, 22350556493, 1100068867451, 1100018536827, 1099984983419, 1099951430011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917876603, 13223959949, 8861887885, 1100152748431, 1100085640607, 1100052087199], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001756575, 1099951425951, 13307774393, 4751463865, 1099867532755, 1099867533779], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867534803, 1099532066271, 4499807713, 1099800356323, 1099800422883, 1099532065255], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56804, 56808, 1099532064239, 16833004, 16833008, 1099548840439], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [33609204, 33609208, 33609212, 67161600, 67161604, 83937800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937804, 34446985745, 83937808, 70622741, 70689301, 100714004], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [100714008, 100714012, 21495049761, 12905186849, 117490208, 117490212], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52817515549, 78168361009, 9885307977, 30739237121, 34799462657, 4969647361], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30923642193, 18072434001, 13223962989, 13089749357, 1100135975279, 1099917874563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884321155, 1099850767747, 1100068862371, 1100052086179, 1100001755555, 1099951424931], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13324552613, 8979323301, 4634027429, 1099850763687, 1099800433063, 1099934576067], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099934642627, 1099934643651, 1099532066263, 1099532065247, 56796, 56800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548841447, 16832996, 16833000, 53740, 16833004, 1099532063219], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [33609200, 33609204, 1099699758587, 1099699759611, 67161592, 67161596], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161600, 4399143429, 1099649360391, 83937796, 83937800, 100713996], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8677329425, 4382365201, 100714000, 100714004, 117490200, 117490204], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [30084912673, 20356641, 117490208, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57011953697, 73856686133, 26410785025, 26243085569, 13375033601, 26712564029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233185597, 13609768253, 8861889909, 1100169527671, 1100119197047, 1100068866423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035313015, 1099968205179, 1099934651771, 1099884321147, 1099850767739, 8861885853], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100085571999, 1099968198075, 1099968199099, 1099934645691, 1099532066255, 1099548842455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56788, 56792, 56796, 1099800356323, 1099800422883, 1099800423907], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532064227, 16832992, 16832996, 50385384, 4533360109, 4432698861], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385388, 3658224, 33609200, 13089668597, 4499803637, 67161588], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161592, 83937788, 83937792, 83937796, 100713992, 100713996], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [87399953, 87466513, 100714000, 117490196, 117490200, 117490204], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [25790013985, 134266400, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61223169061, 56777549881, 26192750877, 17569334557, 4717992221, 22501551405], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26393937197, 9331581229, 1100068865407, 1100018534783, 1099984981375, 1099934650751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901097343, 8861887877, 1100186302855, 1100152749447, 1100085641607, 1099817212295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783658887, 13274219973, 8895436229, 1099901087179, 1099901088203, 1099901089227], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532066251, 1099548842451, 56784, 56788, 56792, 1099532064223], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16832988, 4432699873, 1099800422883, 16832992, 50385380, 50385384], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385388, 67161584, 67161588, 83937784, 83937788, 83937792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099649360391, 1099649426951, 100713988, 100713992, 100713996, 4382365201], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [87399953, 117490192, 117490196, 117490200, 117490204, 134266400], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [21478272549, 12888409637, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61172906025, 43959759933, 22367336741, 22132592933, 17720256805, 17502158129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13156929841, 1099951427959, 1099917874551, 1099867543927, 1099833990519, 1100152749443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102418819, 1100052088195, 1100001757571, 1099951426947, 4566919593, 1100035240363], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100035306923, 1100035307947, 8962544069, 4617248197, 1099917796807, 1099532066247], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548842447, 56780, 56784, 56788, 1099532064219, 16832984], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16832988, 50385376, 50385380, 50385384, 1099750091247, 1099750092271], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161580, 67161584, 67161588, 83937784, 17351080445, 8761216509], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937788, 83937792, 100713988, 100713992, 100713996, 117490192], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [70622741, 70689301, 117490196, 117490200, 134266396, 20290081], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [134266400, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65367278637, 26880623685, 26511377681, 26276569361, 13408517393, 8811629905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018538835, 1099968208211, 1099917872523, 1099867541899, 1099817211275, 8979325325], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828333453, 1100152748431, 1100085640595, 1100035309971, 1099984979347, 1099934648723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099548843459, 13290997189, 8912213445, 1099901087179, 1099901088203, 1099901089227], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532065231, 56780, 56784, 1099548841431, 16832980, 16832984], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16832988, 50385376, 50385380, 50385384, 1099750023663, 1099750024687], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099750091247, 67161580, 67161584, 67161588, 83937784, 83937788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [83937792, 100713988, 100713992, 100713996, 117490192, 4365587989], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [70622741, 117490196, 117490200, 134266396, 134266400, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61089157169, 18357800005, 26394005785, 26175974681, 1100437965083, 1100085644643], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035314019, 1099984983395, 1099934652771, 1099901099363, 8895442301, 1100219857279], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100186303871, 1100119196031, 1100068865407, 9079984561, 8895438257, 1100001683891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099532066243, 1099901087179, 1099901088203, 1099901089227, 1099548842443, 56776], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56780, 56784, 1099548841431, 16832980, 16832984, 16832988], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [50385376, 50385380, 50385384, 67161580, 67161584, 67161588], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [83937784, 4399144445, 1099682981375, 83937788, 83937792, 100713988], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [100713992, 100713996, 117490192, 117490196, 53845529, 53912089], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [117490200, 117490204, 134266400, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65283529781, 1295440973, 22166150405, 26192753925, 9080066309, 8878667117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186304879, 1100135974255, 1100085643631, 1100035313007, 1099917873535, 1099867542911], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817212287, 1099750104455, 8912215469, 4566919597, 1100018528687, 1099984975287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984976311, 1099951422903, 1099532066243, 1099548842443, 56776, 56780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56784, 1099532064215, 16832980, 16832984, 33609180, 50385376], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [50385380, 50385384, 67161580, 1099733314035, 1099733315059, 67161584], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [67161588, 83937784, 4399144445, 154576381, 83937788, 83937792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [100713988, 100713992, 100713996, 117490192, 117490196, 53845529], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53912089, 117490200, 117490204, 134266400, 42532, 134266404], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group1
