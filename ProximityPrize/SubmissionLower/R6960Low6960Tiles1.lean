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
  ⟨unpack [2332101637, 1023479817, 4613805065, 18438953997, 86589190161, 86959424557], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10136901705, 14865601625, 31560446137, 35637711033, 52364801209, 27047235841], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30605027629, 26243025197, 35385978173, 22132389249, 21931134337, 17569129857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100119067043, 1100119068067, 1100119069091, 1100119070115, 8811493809, 1100051957171], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001696191, 1100001697215, 1100001698239, 4566853089, 4482969057, 1099850626531], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099817073131, 1099817074155, 1099817075179, 30353215981, 21763355117, 13106384369], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4533231089, 1099649297939, 1099649298963, 12938611233, 53782053, 1099565410855], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4331969065, 20226605, 8593312305, 8593380913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i51 : checks (tilesOf batches) 140 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9513015307, 27230807053, 65467138073, 86892314669, 14331204681, 31409314025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31258853653, 31007400213, 30772658461, 34849595677, 30504437021, 35134454125], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13072909705, 13240607125, 13140013461, 8811495829, 1099951297959, 1099968141735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934588327, 1099917812135, 1099934518715, 1099900965307, 13324419529, 8979190217], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8844975561, 1099934515663, 1099934516687, 1099900963279, 1099900957143, 1099900958167], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099900959191, 1099900960215, 1099800291823, 1099800292847, 26007986681, 13123091961], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4415856137, 1099682850315, 57864, 56844, 57868, 1099548710419], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56848, 57872, 55828, 56852, 57876, 1099548709403], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55832, 56856, 57880, 54812, 55836, 56860], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57884, 1099548708387, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 34396518953], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4331901481, 4331969065, 37003817, 53800, 54824, 55848], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56872, 57896, 34379668013, 1099531930159, 52780, 53804], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54828, 55852, 56876, 57900, 52784, 53808], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27230807053, 56977866777, 86825138217, 22803631173, 30839699721, 34916702473], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39043972361, 31141413165, 26712432941, 17434983785, 35184715117, 1100051960199], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018406791, 1100001630599, 1100001697159, 1099968143751, 13274159505, 13139945873], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8828270993, 1100018402731, 1099984849323, 1099934518699, 13341195717, 9012743621], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099934513615, 1099934514639, 1099900961231, 1099917732307, 1099917733331, 1099917734355], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099917735379, 4482898417, 4432634353, 57844, 57848, 1099531934207], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56828, 57852, 1099548710403, 56832, 57856, 55812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56836, 57860, 1099548709387, 55816, 56840, 57864], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 25890546193, 1099548708371], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 1099632517655, 1099632518679], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 53784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 1099531930143, 52764], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 4331969057], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099548706343, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56868, 57892, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55848, 56872, 57896, 4315123245, 4315190829, 20225581], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [1099531928111, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56876, 57900, 30068001329, 21478140465, 50736, 51760], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52784, 53808, 54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
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
private theorem i49 : checks (tilesOf batches) 140 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40015638545, 86707427361, 56878083133, 31158261989, 30957140197, 43489859813], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21780284729, 4684307769, 35235049817, 26678875481, 17619458409, 13240610153], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13156793705, 1100035181959, 1100001628551, 1099968075143, 1099934521735, 1099850702235], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099833926043, 1100035177903, 1099984847279, 1099951293871, 1099900963247, 17585830333], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [9012743613, 1099984842179, 1099984843203, 1099984844227, 1099984845251, 4566784469], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4482900437, 1099900955095, 57832, 17468387821, 1099531934191, 56812], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57836, 56816, 57840, 1099531933175, 55796, 56820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57844, 55800, 56824, 57848, 1099531932159, 54780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55804, 56828, 57852, 54784, 55808, 56832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57856, 1099699626503, 1099699627527, 1099548708359, 53764, 54788], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55812, 56836, 57860, 53768, 54792, 55816], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56840, 57864, 1099548707343, 53772, 54796, 55820], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56844, 57868, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56848, 57872, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56852, 57876, 104045081, 104111641, 1099531929115, 51736], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57884, 8660420129, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 4348678693], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55844, 56868, 57892, 49704, 50728, 51752], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [34379674157, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 57900, 48688], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [49712, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25]
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
private theorem i52 : checks (tilesOf batches) 140 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44310936597, 86724405285, 39782169665, 31024179437, 30806214893, 34899994861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13106466129, 1100068740435, 1100085584211, 30956928349, 26544659805, 13207054705], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106461041, 1100119066995, 1099968073099, 1099934519691, 1099900966283, 1099901032843], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13307644321, 8962415009, 8828200353, 1100051954091, 1100001623467, 1099968070059], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099917739435, 1099984843203, 1099984844227, 13274085845, 1099531935195, 1099867399647], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099867400671, 1099867401695, 57820, 56800, 57824, 56804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57828, 1099531933163, 55784, 56808, 57832, 55788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56812, 57836, 1099548709363, 54768, 55792, 56816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57840, 54772, 55796, 56820, 57844, 1099548708347], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 1099733113343, 1099733114367], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099733180927, 53756, 54780, 55804, 56828, 57852], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 57856, 1099531930119], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8744307209, 4399011337, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56840, 57864, 50700, 51724, 52748, 53772], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 50704, 51728], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [1099515151895, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56852, 57876, 25873767961, 49688, 50712, 51736], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55836, 56860, 57884, 48672, 49696, 50720], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [57888, 53712421, 48676, 49700, 50724, 51748], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [48680, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54824, 55848, 56872, 57896, 47660, 48684], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49708, 50732, 51756, 52780, 53804, 54828], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55852, 56876, 57900, 4298345009, 3379761, 47664], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [48688, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 140 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52766918681, 86690987053, 18374447177, 35050781933, 34883150061, 30521214189], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31057660225, 22383978817, 8845051229, 1100035182955, 1100001629547, 1099968076139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968142699, 1099934589291, 13274161517, 8912089453, 8845049197, 13458637205], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13274157461, 1099884186015, 1099850632607, 1099968069039, 1099917738415, 1099867407791], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001620415, 1100001621439, 1099951290815, 1099934441935, 1099934442959, 1099934509519], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099934510543, 57808, 57812, 1099531934171, 56792, 57816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56796, 57820, 1099531933155, 55776, 56800, 57824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55780, 56804, 57828, 1099531932139, 54760, 55784], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56808, 57832, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548708339, 53744, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4516450805, 1099766667767, 1099766668791, 53748, 54772, 55796], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56820, 57844, 51704, 53752, 54776, 55800], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56824, 57848, 1099531930111, 52732, 53756, 54780], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55804, 56828, 57852, 52736, 53760, 54784], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55808, 56832, 57856, 50692, 51716, 52740], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 50696], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57864, 50700, 51724, 52748, 53772, 54796], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55820, 56844, 57868, 49680, 50704, 51728], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [49684, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55828, 56852, 57876, 49688, 50712, 51736], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [21562026525, 48668, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 8660419105], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [4365454881, 48672, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 48676], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55844, 56868, 57892, 47656, 48680, 49704], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [56872, 57896, 20223533, 47660, 48684, 49708], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [56876, 57900, 30068001329, 47664, 48688, 49712], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [56978134045, 86640725041, 1295310925, 30772661477, 30621805797, 21981613285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26829804849, 22333649201, 22115682609, 1100068736355, 1100035182947, 1100001629539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968076131, 1099917745507, 13139946861, 8811494765, 1100068735343, 1099783594375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8912085393, 1099968069031, 1099917738407, 1099867407783, 1100068728239, 1100068729263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100035175855, 1099984845231, 1099548712391, 57800, 8979188173, 4633892301], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4516453837, 57804, 1099531934163, 56784, 57808, 56788], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57812, 1099531933147, 55768, 56792, 57816, 55772], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56796, 57820, 1099850622435, 1099850623459, 1099531932131, 54752], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55776, 56800, 57824, 54756, 55780, 56804], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57828, 1099548708331, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57832, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 51700], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51704, 52728, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57848, 50684, 51708, 52732, 53756, 54780], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55804, 56828, 57852, 17384501761, 8794637825, 50688], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51712, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57856, 1099699559943, 1099699626503, 50692, 51716, 52740], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 49672], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50696, 51720, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56840, 57864, 49676, 50700, 51724, 52748], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 49680], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50704, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56848, 57872, 48660, 49684, 50708, 51732], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [48664, 49688, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 48668, 49692], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [56860, 57884, 70489633, 70556193, 47648, 48672], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [55840, 56864, 57888, 47652, 48676, 49700], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [56868, 57892, 47656, 48680, 49704, 50728], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [57896, 20156973, 46636, 47660, 48684, 49708], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [56876, 57900, 30068069937, 46640, 47664, 48688], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [49712, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61222969377, 73823001653, 30588181753, 30420483321, 4818525433, 26729210153], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26444135721, 21981468969, 13140016465, 8794721617, 1100001630547, 8828203385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099833924987, 1099800371579, 1099900964231, 1099867410823, 1099817080199, 1100035177875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984847251, 1099934516627, 1099900963219, 8912083365, 1100102215079, 1100102216103], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100102217127, 1100035174839, 1100001621431, 1099934513591, 57792, 57796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099531934155, 56776, 57800, 13290864077, 8928857549, 56780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57804, 1099548710355, 55760, 56784, 57808, 55764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56788, 57812, 55768, 56792, 57816, 1099531932127], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54748, 55772, 56796, 57820, 54752, 55776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56800, 57824, 1099548708327, 53732, 54756, 55780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56804, 57828, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57832, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51696, 52720, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57840, 1099766667767, 1099766668791, 1099766735351, 51700, 52724], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 50680], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51704, 52728, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57848, 50684, 51708, 52732, 53756, 54780], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55804, 56828, 57852, 50688, 51712, 52736], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 57856, 49668], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50692, 51716, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56836, 57860, 49672, 50696, 51720, 52744], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 57864, 49676], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50700, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56844, 57868, 25890546193, 48656, 49680, 50704], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [57872, 48660, 49684, 50708, 51732, 52756], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 48664], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55832, 56856, 57880, 47644, 48668, 49692], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [56860, 57884, 4365454881, 70489633, 47648, 48672], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [55840, 56864, 57888, 47652, 48676, 49700], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [56868, 57892, 47656, 48680, 49704, 50728], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [57896, 46636, 47660, 48684, 49708, 50732], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [57900, 21478138417, 12888275505, 4298345009, 46640, 47664], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [48688, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 140 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [73889836069, 48187487293, 26762767609, 26511247609, 26293216505, 17535648033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13156799777, 1099934520679, 1099900967271, 1099867413863, 1099867480423, 13156722041], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100236502395, 1100186171771, 1100135841147, 1100085510523, 1100035179899, 1099984849275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934518651, 1099900965243, 9079785901, 8945636781, 4600340909, 1100001552831], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001619391, 1100001620415, 1099531935167, 57788, 57792, 1099531934151], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56772, 57796, 56776, 57800, 1099548710351, 55756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56780, 57804, 55760, 56784, 57808, 55764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56788, 57812, 1099531932123, 54744, 55768, 56792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57816, 54748, 55772, 56796, 57820, 1099548708323], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53728, 54752, 55776, 56800, 57824, 53732], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54756, 55780, 56804, 57828, 21746576873, 8895301097], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53736, 54760, 55784, 56808, 57832, 51692], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52716, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51696, 52720, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57840, 51700, 52724, 53748, 54772, 55796], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56820, 57844, 1099749958139, 1099749959163, 50680, 51704], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52728, 53752, 54776, 55800, 56824, 57848], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [50684, 51708, 52732, 53756, 54780, 55804], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56828, 57852, 50688, 51712, 52736, 53760], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 4399011333, 1099699559943], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [49668, 50692, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55812, 56836, 57860, 49672, 50696, 51720], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [49676, 50700, 51724, 52748, 53772, 54796], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [55820, 56844, 57868, 48656, 49680, 50704], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [57872, 48660, 49684, 50708, 51732, 52756], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 48664], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [55832, 56856, 57880, 47644, 48668, 49692], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [56860, 57884, 70489633, 70556193, 47648, 48672], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [55840, 56864, 57888, 4331901477, 47652, 48676], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [55844, 56868, 57892, 46632, 47656, 48680], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [55848, 56872, 57896, 17199951405, 8610087469, 46636], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [47660, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 57900, 3379761], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [46640, 47664, 48688, 49712, 50736, 51760], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [52784, 53808, 54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69611714601, 39647951937, 26628618497, 26393875713, 21981540609, 17401432369], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068740403, 1100018409779, 1100035180907, 1099984850283, 1099951296875, 1099900966251], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867412843, 1100236435839, 1100219725183, 1100169394559, 1100102286719, 1100051956095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001625471, 9029522841, 8861753753, 1100152548763, 1099548713391, 1099531935163], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57784, 57788, 1099531934147, 56768, 57792, 56772], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57796, 1099548710347, 55752, 56776, 57800, 55756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56780, 57804, 17518721489, 8928857553, 55760, 56784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57808, 1099531932119, 54740, 55764, 56788, 57812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54744, 55768, 56792, 57816, 1099867333087, 1099867399647], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099867400671, 52700, 53724, 54748, 55772, 56796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57820, 1099531931107, 53728, 54752, 55776, 56800], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57824, 53732, 54756, 55780, 56804, 57828], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51688, 52712, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57832, 51692, 52716, 53740, 54764, 55788], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56812, 57836, 51696, 52720, 53744, 54768], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55792, 56816, 57840, 50676, 51700, 52724], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 50680], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51704, 52728, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57848, 50684, 51708, 52732, 53756, 54780], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55804, 56828, 57852, 49664, 50688, 51712], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [52736, 53760, 54784, 55808, 56832, 57856], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [187931141, 1099699559943, 49668, 50692, 51716, 52740], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 49672], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [50696, 51720, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [56840, 57864, 48652, 49676, 50700, 51724], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [48656, 49680, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 48660, 49684], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [56852, 57876, 48664, 49688, 50712, 51736], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [47644, 48668, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 47648], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [48672, 49696, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [54816, 55840, 56864, 57888, 12938607141, 8643643941], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [53712421, 47652, 48676, 49700, 50724, 51748], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [46632, 47656, 48680, 49704, 50728, 51752], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [1099531858479, 46636, 47660, 48684, 49708, 50732], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [57900, 46640, 47664, 48688, 49712, 50736], by decide +kernel⟩
private def p42 : P :=
  ⟨unpack [51760, 52784, 53808, 54832, 55856, 56880], by decide +kernel⟩
private def p43 : P :=
  ⟨unpack [57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69578228781, 26830161989, 26544801021, 26309992701, 21897657597, 1100051961159], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100001630535, 1099968077127, 1099968143687, 8811494757, 1100051958119, 1100001627495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951296871, 8979194241, 8828202369, 1100152617347, 1099968069023, 1099917738399], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867407775, 1099531935159, 57780, 13274088889, 8912082361, 57784], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001619391, 1100001620415, 1099951289791, 1099548711359, 56764, 57788], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56768, 57792, 56772, 57796, 1099531933131, 55752], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56776, 57800, 55756, 56780, 57804, 1099548709331], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54736, 55760, 56784, 57808, 54740, 55764], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56788, 57812, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52700, 53724, 54748, 55772, 56796, 57820], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099850555875, 1099850622435, 1099850623459, 1099531931107, 53728, 54752], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55776, 56800, 57824, 53732, 54756, 55780], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56804, 57828, 51688, 52712, 53736, 54760], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55784, 56808, 57832, 51692, 52716, 53740], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54764, 55788, 56812, 57836, 51696, 52720], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 50676], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51700, 52724, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57844, 50680, 51704, 52728, 53752, 54776], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55800, 56824, 57848, 50684, 51708, 52732], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 57852, 49664], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [50688, 51712, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [56832, 57856, 49668, 50692, 51716, 52740], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 4399011337], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [1099682848267, 49672, 50696, 51720, 52744, 53768], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 48652, 49676], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50700, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56844, 57868, 48656, 49680, 50704, 51728], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [48660, 49684, 50708, 51732, 52756, 53780], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 8693974553, 4399010329], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [48664, 49688, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 47644, 48668], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [55836, 56860, 57884, 47648, 48672, 49696], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [56864, 57888, 53778981, 47652, 48676, 49700], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [56868, 57892, 46632, 47656, 48680, 49704], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [56872, 57896, 46636, 47660, 48684, 49708], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [56876, 57900, 46640, 47664, 48688, 49712], by decide +kernel⟩
private def p42 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p43 : P :=
  ⟨unpack [56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73789378609, 9767802953, 30705553645, 26276507885, 21880949997, 1100085513555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035182931, 1100001629523, 1099867412839, 1099833859431, 1099833925991, 8895312233], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811494761, 1100035180907, 13307646345, 8945639817, 1100219657611, 1099968069027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099900961187, 1099850630563, 1100035174839, 1100001621431, 1099934513591, 1099531935159], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57780, 57784, 1099531934143, 56764, 57788, 56768], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57792, 55748, 56772, 57796, 1099531933131, 55752], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56776, 57800, 55756, 56780, 57804, 1099548709331], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54736, 55760, 56784, 57808, 54740, 55764], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56788, 57812, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52700, 53724, 54748, 55772, 56796, 57820], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099850555875, 1099850622435, 1099850623459, 1099531931107, 53728, 54752], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55776, 56800, 57824, 53732, 54756, 55780], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56804, 57828, 51688, 52712, 53736, 54760], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55784, 56808, 57832, 51692, 52716, 53740], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54764, 55788, 56812, 57836, 4566782449, 4449343985], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51696, 52720, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57840, 50676, 51700, 52724, 53748, 54772], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55796, 56820, 57844, 50680, 51704, 52728], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 57848, 50684], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [51708, 52732, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [57852, 49664, 50688, 51712, 52736, 53760], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 49668, 50692], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [51716, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [57860, 49672, 50696, 51720, 52744, 53768], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 49676, 50700], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [51724, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [57868, 48656, 49680, 50704, 51728, 52752], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 48660], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [49684, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [55828, 56852, 57876, 104045081, 104111641, 48664], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [55832, 56856, 57880, 47644, 48668, 49692], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [56860, 57884, 47648, 48672, 49696, 50720], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [57888, 47652, 48676, 49700, 50724, 51748], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [47656, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 46636], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [47660, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 57900, 46640], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [47664, 48688, 49712, 50736, 51760, 52784], by decide +kernel⟩
private def p42 : P :=
  ⟨unpack [53808, 54832, 55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73755892789, 30655290601, 26209402089, 9096714473, 8895380821, 1100119066967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068736343, 1100018405719, 1099968075095, 1099867412839, 1099817082215, 1099817148775], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13257383289, 8878534009, 1100186171771, 1099968069027, 1099900961187, 1099850630563], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099548712371, 57776, 57780, 57784, 1099531934143, 56764], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57788, 1099984842179, 1099984843203, 1099951289795, 56768, 57792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548710343, 55748, 56772, 57796, 55752, 56776], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57800, 55756, 56780, 57804, 1099548709331, 54736], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55760, 56784, 57808, 4516453845, 221488597, 1099900955095], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54740, 55764, 56788, 57812, 54744, 55768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56792, 57816, 52700, 53724, 54748, 55772], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56796, 57820, 1099531931107, 53728, 54752, 55776], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56800, 57824, 53732, 54756, 55780, 56804], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57828, 51688, 52712, 53736, 54760, 55784], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56808, 57832, 51692, 52716, 53740, 54764], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55788, 56812, 57836, 51696, 52720, 53744], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 50676, 51700], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [50680, 51704, 52728, 53752, 54776, 55800], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56824, 57848, 50684, 51708, 52732, 53756], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 49664, 50688], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51712, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [57856, 49668, 50692, 51716, 52740, 53764], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 49672, 50696], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [57864, 154443277, 87335437, 20227597, 49676, 50700], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [51724, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [57868, 48656, 49680, 50704, 51728, 52752], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 42516], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [48660, 49684, 50708, 51732, 52756, 53780], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 42520, 48664], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [55832, 56856, 57880, 42524, 47644, 48668], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [55836, 56860, 57884, 42528, 47648, 48672], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [55840, 56864, 57888, 41508, 42532, 47652], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [48676, 49700, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [54820, 55844, 56868, 57892, 41512, 42536], by decide +kernel⟩
private def p38 : P :=
  ⟨unpack [47656, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p39 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 41516], by decide +kernel⟩
private def p40 : P :=
  ⟨unpack [42540, 46636, 47660, 48684, 49708, 50732], by decide +kernel⟩
private def p41 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p42 : P :=
  ⟨unpack [57900, 41520, 42544, 46640, 47664, 48688], by decide +kernel⟩
private def p43 : P :=
  ⟨unpack [49712, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p44 : P :=
  ⟨unpack [55856, 56880, 57904], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43, p44]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 140 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((1 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
