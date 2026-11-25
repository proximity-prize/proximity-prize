import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass7

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2181106693, 1006702601, 5956244489, 19244784653, 44529168401, 138247494689], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43993292005, 52314999013, 35202383077, 35503542525, 43490030989, 26226559393], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17636697505, 13274626465, 13123701169, 4550547889, 38842950113, 4416326125], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649765871, 1099649766895, 1099632990707, 1099632991731, 8644180481, 4349216257], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3919372], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 131 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14680922121, 31945926673, 69896849433, 86993439793, 39564101941, 35185455413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30756410681, 34833347897, 5003532601, 13190739373, 8845444525, 4567323053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39010507193, 4533469653, 21663225313, 8778329569, 1099683322343, 1099683323367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382770669, 1099649764847, 1099632988659, 1099632989683, 4382767609, 4365992441], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30135644669, 70947325, 1099549100551, 20693516], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27701027853, 48774201369, 112511447081, 1631247437, 39564243189, 47852329205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18005805301, 43490099593, 30622117257, 21914818953, 17536037257, 8946107785], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851092415, 1099851093439, 1099851094463, 21713489361, 1099750432215, 43154548189], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8727998945, 4416257505, 4382770657, 1099700096483, 8694441461, 1099599431163], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599432187, 54246913, 54247937, 4332368389, 37468677, 25773494797], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21478673933], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 131 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36207669265, 74108130333, 69813640245, 39547393317, 26696187173, 30722857253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30454495549, 4869314877, 8912550301, 8811890077, 1099985310111, 1099985311135], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190666693, 8895769029, 4567250373, 1099800762827, 1099800763851, 43221660109], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750426071, 1099750427095, 1099750428119, 138132973, 1099649761775, 34430541309], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21512159749, 20624905, 20691465], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 131 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44579830805, 78336190501, 44178125885, 31074969885, 30806673693, 22166481181], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21730345317, 4667988325, 43422989725, 8761557413, 1099951754663, 1099951755687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951756711, 1099834317251, 1099834318275, 8862214597, 4533695941, 1099817467335], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21713488337, 8845435345, 1099767202259, 1099767203283, 1099767204307, 54179329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54245889, 4315590153, 21478672909], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48774334489, 82564184105, 22820800581, 30974376209, 34933872913, 9399090449], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39211911561, 26327150985, 8795113865, 1100069197195, 1100069198219, 1100069199243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13358438813, 13207513501, 1099985238431, 1099851090367, 1099851091391, 1099851092415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750358487, 1099750425047, 1099750426071, 8727924205, 4433029613, 4382700013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37401093, 37402117], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48791311389, 78269285421, 14281265225, 30857004309, 30622197013, 9281651989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39161648529, 21998632337, 1100002087323, 1100002088347, 1100002089371, 1099985313179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13241066909, 8862217629, 1099985240479, 1099851089343, 1099851090367, 1099851091391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13123556821, 4382701025, 1099700026851, 8677664245, 104509941, 1099599361531], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599428091, 38658397709, 4298810893, 3845644, 56844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57163276321, 73940834357, 30672460053, 30504827157, 4886026517, 35084788065], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22166406497, 13140408705, 8778336641, 1100102751619, 1099951757735, 1099918204327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13240999337, 8895770025, 1099901422003, 1099901423027, 1099901424051, 4449810881], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834245571, 1099834312131, 1099666471403, 1099666537963, 4382698997, 1099616138743], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644107777, 4349143553, 21495383561, 56840, 3846668, 56844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65551952933, 52600286269, 30974373173, 26444598581, 21998709045, 17569595709], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962889021, 1100002088347, 1099985312155, 1099951758747, 1099985240479, 1099985241503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985242527, 1099985309087, 1099985310111, 8878991797, 4550473141, 1099884576183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17401744857, 8811880921, 1099616138743, 1099616139767, 4349144573, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 20622860, 16833036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65535309865, 39799339073, 26662631733, 22166410549, 17737297205, 17468932437], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8879068501, 1099985240479, 1099985241503, 1099985242527, 1099985309087, 1099985310111], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985311135, 1099968534943, 1099918204319, 8811883965, 4466588093, 17351480797], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4500138461, 1099666471403, 1099666537963, 104509941, 1099616138743, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 12905518601, 20620809, 56840, 25773570573, 16833036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 131 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69729682477, 22736914501, 30823449889, 26327229729, 13459177761, 1100153082231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153083255, 1100119529847, 1100085976439, 13190735273, 8795108777, 1099918131631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918132655, 1099918199215, 1099918200239, 21696710105, 13090069977, 1099716802015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716803039, 1099716804063, 4382698997, 56832, 56836, 16833032], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8593776141, 4298811917, 3846668, 16833036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61206925361, 18475502661, 22233518389, 21998709045, 9164210485, 1100119461247], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119527807, 1100119528831, 1100085975423, 1100035644799, 8895769013, 4550473141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884576183, 1099834245571, 1099834312131, 1099834313155, 17317925357, 8711218669], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616138743, 1099616139767, 56828, 54178305, 56832, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833032, 4298810893, 3845644, 16833036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65367678005, 1429920845, 30655749401, 26193083673, 1100455008539, 8878996865], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102683011, 1100102684035, 1100102750595, 1100102751619, 1099867872679, 13257776553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895770025, 1099934906795, 1099800690123, 1099800691147, 1099800757707, 4399476213], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [104510965, 1099549104639, 56828, 56832, 12922297861, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833032, 16833036], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 131 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group7
