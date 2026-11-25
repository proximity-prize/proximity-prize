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
  ⟨unpack [2231438341, 1006702601, 5301801995, 19060104205, 65433382929, 87026724905], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31561598021, 31258710269, 39815426309, 35487111429, 35084664121, 34933809465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106726317, 13039687085, 17468793285, 13106722245, 1099800630743, 1099800631767], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800632791, 1099800633815, 4432971237, 1099733519847, 1099733520871, 25974767081], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17384905193, 4416124413, 4365794813, 1099582522891, 1099582523915, 8643980813], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315528721, 34380077589, 3784217, 3785241], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 134 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10671036427, 27583456269, 86774464537, 82698409013, 39832273133, 39614376173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52180717805, 30471144765, 21981794697, 17569393033, 17468800393, 8811827617], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018736547, 1100018737571, 43288569281, 4483235281, 1099817338323, 1099817404883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817405907, 30353549781, 21730134485, 1099783852507, 1099783853531, 1099783854555], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8778197481, 4449678825, 38775560701, 1099616009731, 1099616076291, 8677532165], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [38725374473, 37271057, 37272081, 38675038741, 17200286229, 12905389589], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4298681881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i54 : checks (tilesOf batches) 134 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27583456269, 52901265433, 86892508201, 27165968453, 35168548121, 39195154713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833219865, 39429816673, 30806468961, 13140279693, 1100068999575, 8778274197], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069069207, 13375084957, 13257714077, 13123500445, 43288569281, 1099867739591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867740615, 1099867741639, 1099834116559, 1099834183119, 4432902617, 1099783782875], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783783899, 17435167197, 4432898553, 4365791737, 1099632785919, 1099632786943], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54047245, 1099565676047, 42969933333, 30085179925, 8610422293], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 134 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40200450065, 86791575585, 56979008573, 35436779769, 39413185785, 43490190585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17485582673, 17552614781, 13207386493, 13106727293, 39278752133, 1100035512735], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018736543, 1099985183135, 21914615217, 13307975089, 1099934779831, 1099934780855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934847415, 1099934848439, 4449679821, 1099834114511, 1099834115535, 8794973657], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466455001, 1099666340343, 1099666341367, 34480740861, 87601669, 1099599230471], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4349011469, 54046221, 57872, 57876, 12888610329, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i52 : checks (tilesOf batches) 134 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44512590869, 78302504997, 48389076029, 31041284373, 30806542613, 30605289749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21730216273, 1100270395731, 39245266317, 30638695821, 1100085774739, 1100085775763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085776787, 1100085843347, 1100069067155, 1100035513747, 13207382425, 8845310361], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100052219291, 17502276041, 8895569353, 1099783780827, 1099783781851, 1099783782875], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466452969, 1099716669931, 1099716670955, 17284171265, 57864, 57868], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56848, 57872, 8610422293, 20490773, 20491797, 56852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57876, 30068401689, 8593644057, 55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i55 : checks (tilesOf batches) 134 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52901398553, 82513722413, 22770338885, 30907137289, 34900188425, 34766110985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39362709857, 26494726497, 13157056877, 1100152885631, 1100102555007, 1100119398783], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069068159, 1100035514751, 13324754317, 13190606221, 8828534157, 1099951557043], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951558067, 1099850890699, 1099850891723, 1099850892747, 13173755349, 4466453977], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783779803, 1099783780827, 8711085561, 4382566905, 57852, 57856], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099599229447, 56836, 57860, 56840, 57864, 38708595213], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099548972559, 56844, 57868, 25806991889, 37267985, 37269009], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 56848, 57872, 55828, 56852, 57876], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4298677785, 4298679833, 1099515417115, 54808, 55832, 56856], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61340537885, 82463461425, 1413013581, 30789767425, 30588514561, 17720463617], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35218740545, 22367533377, 13190607233, 8828535169, 1100152884611, 1100085776775], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085843335, 1100052289927, 1100018736519, 1099867742627, 13307974065, 8912347569], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8811752881, 1099901223359, 1099901224383, 1099901225407, 1099834112463, 1099834113487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716668907, 1099716669931, 1099716670955, 57848, 57852, 4399342081], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [104376833, 56832, 57856, 56836, 57860, 55816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56840, 57864, 55820, 56844, 57868, 34396853777], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548971539, 54800, 55824, 56848, 57872, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 57876, 21478472217, 12888609305, 54808], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65551753249, 69612183609, 26394206481, 26192887057, 9096976657, 31041282353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511507761, 26293542193, 13106724217, 1100169661819, 1100119331195, 1100085777787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001958287, 1099951627663, 1099918074255, 1099985107371, 8962678193, 8862083505], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4516787633, 1099951553971, 1099951554995, 1099951556019, 1099951557043, 21663023589], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8811747813, 1099716670955, 57840, 4382566901, 1099666338295, 57844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56824, 57848, 56828, 57852, 56832, 57856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532195335, 55812, 56836, 57860, 55816, 56840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57864, 4332234253, 1099565673999, 1099548971535, 54796, 55820], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56844, 57868, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17200284181, 8610420245, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [3712537, 3713561, 1099515416091, 53784, 54808, 55832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 134 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65518267429, 56811236413, 26192882985, 21797325097, 1100287107371, 26763095341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478020909, 22015354157, 1100186438011, 1100152884603, 1100102553979, 1100069000571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069067131, 1100018736507, 8778202513, 8895636913, 4567118257, 1099951552947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884445123, 1099884446147, 1099884447171, 17435167193, 8845303257, 1099532198375], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57836, 57840, 1099666338295, 1099666339319, 56820, 57844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56824, 57848, 121154045, 1099632782847, 56828, 57852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532195331, 55808, 56832, 57856, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57860, 1099548971531, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 54800, 55824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 57872, 1099532193303, 53780, 54804, 55828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56852, 57876, 12888541721, 8593644057, 3712537, 53784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54808, 55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69712640041, 39748877377, 26729609497, 26427692313, 21998579993, 13190613321], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828541257, 1100001958279, 1099968404871, 1099918074247, 1100068997527, 1100035444119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985113495, 1099985180055, 8862085529, 1100052217243, 1100052218267, 1100052219291], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13224089017, 8878859705, 1099767001567, 1099767002591, 1099767003615, 57832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57836, 57840, 56820, 57844, 56824, 57848], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55804, 56828, 57852, 21579135489, 12989207041, 4382565889], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099616005635, 55808, 56832, 57856, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57860, 1099548971531, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4349010445, 54796, 55820, 56844, 57868, 54800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55824, 56848, 57872, 1099532193303, 53780, 54804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55828, 56852, 57876, 3713561, 53784, 54808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73940632621, 22669675589, 26628949261, 30622064909, 26176176397, 1100085845351], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052291943, 8862089585, 1100186439027, 1100136108403, 1100085777779, 1100085844339], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9046565269, 8929193365, 8794978709, 1099934778807, 1099934779831, 1099850889675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850890699, 1099850891723, 17435166173, 8845236701, 205041129, 1099716669931], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716670955, 57832, 57836, 56816, 57840, 56820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57844, 56824, 57848, 1099548972543, 55804, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57852, 55808, 56832, 57856, 4382565893, 55812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56836, 57860, 1099532194315, 54792, 55816, 56840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57864, 54796, 55820, 56844, 57868, 53776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 1099532193303, 53780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 53784, 54808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82379575345, 1345904717, 30873653485, 30622068973, 17720463597, 1100136108403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085777779, 1100085844339, 1100035513715, 13224161653, 8845312373, 1100169661815], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099850965395, 13324751281, 8929124785, 8811752881, 1099934777783, 1099934778807], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934779831, 1099850889675, 1099850890699, 57828, 205041129, 1099716669931], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716670955, 57832, 57836, 56816, 57840, 56820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57844, 56824, 57848, 1099532195327, 55804, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57852, 55808, 56832, 57856, 4382564869, 87599621], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 1099532194315, 54792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55816, 56840, 57864, 54796, 55820, 56844], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57868, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099532193303, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73840041013, 30689107197, 26243218685, 9130531069, 8912420209, 1100219992435], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186439027, 1100136108403, 1100085777779, 1100018735491, 1099968404867, 1099918074243], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13291199893, 8945970581, 8794978709, 1099884447171, 1099850889675, 1099850890699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850891723, 57828, 57832, 188263917, 1099699892719, 1099699893743], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57836, 56816, 57840, 56820, 57844, 8727862777], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4382566905, 56824, 57848, 1099532195327, 55804, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57852, 55808, 56832, 57856, 54788, 55812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56836, 57860, 1099532194315, 54792, 55816, 56840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57864, 54796, 55820, 56844, 57868, 37267985], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 1099532193303], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 53784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54808, 55832, 56856, 57880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
