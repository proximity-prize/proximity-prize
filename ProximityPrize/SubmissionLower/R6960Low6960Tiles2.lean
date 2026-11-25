import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass2

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 1023479817, 4613805065, 18539682829, 86589190161, 86976267309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10136901705, 14848889945, 31610843321, 35637711033, 52398421177, 31241605377], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30588250417, 26226247985, 22132454793, 17736895881, 17602748809, 8811563425], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100102358435, 8845047217, 8794784177, 1099984918975, 1099984919999, 1099984921023], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867475419, 1099867476443, 1099817140711, 1099817141735, 1099817142759, 30336504301], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21746643437, 4533297649, 4449413617, 4415926769, 1099766807027, 1099766808051], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [13005786641, 4415856145, 1099632587283, 1099632588307, 87403033, 1099599031835], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [34429997597, 12905122345, 38657930797, 3515949], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9697630217, 27297981453, 65467138073, 86909157421, 14331204681, 31241804053], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35419668757, 31007466773, 30755947809, 30605026593, 30487659809, 35100965245], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106529673, 13173564837, 8828269989, 8778006949, 1100001695143, 1099968141735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934588327, 1099917812135, 1099951361475, 1099917808067, 13307708873, 8979256777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8845042121, 1099884249559, 1099884250583, 1099884251607, 1099833914851, 1099833915875], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099833916899, 1099783515631, 1099783582191, 25974433273, 13106381305, 4382302729], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099666074123, 1099532001803, 1099548777999, 57872, 25873767957, 1099548776983], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57876, 56856, 57880, 54812, 56860, 57884], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53781025, 1099565409827, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 4315190825], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [20225577, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17183242797, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27297981453, 56977866777, 86841980969, 22820473925, 30856542477, 34933545229], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34799402253, 31141478701, 26762830125, 13123239289, 35100894589, 1100119133579], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085580171, 1100052026763, 1100018473355, 1099984919947, 1099968143755, 13240605081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13140011417, 8794716569, 1100018468279, 1099968137655, 17535565261, 8928858573], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099917801935, 1099917802959, 1099917803983, 1099867400667, 1099867401691, 1099867402715], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099867469275, 4482964977, 1099766736371, 1099532001787, 1099548777983, 57856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55812, 57860, 55816, 56840, 57864, 54796], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55820, 56844, 57868, 54800, 55824, 56848], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57872, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 25840280093], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4348744225, 4331969057, 1099565408803, 52768, 53792, 54816], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55840, 56864, 57888, 12921830949, 8626933285, 51748], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57896, 3447341, 3448365, 51756, 52780, 53804], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40015638545, 82479634465, 61173049401, 31141550325, 30923651317, 34983876853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21847391541, 13257528629, 35251892569, 30856467801, 13257382285, 13156788621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100186171791, 1100152618387, 1100152684947, 1100119131539, 1100068800915, 1100035247507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001694099, 1099968140691, 1099934587283, 1099901033875, 1099867480467, 17602673093], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8979189189, 1099900955091, 1099900956115, 1099900957139, 1099901023699, 4533295593], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4432634345, 1099532001771, 56816, 57840, 56820, 57844], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17401345529, 55800, 56824, 57848, 55804, 56828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57852, 54784, 55808, 56832, 57856, 54788], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55812, 56836, 57860, 53768, 54792, 55816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56840, 57864, 1099649294863, 1099649295887, 53772, 54796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55820, 56844, 57868, 52752, 53776, 54800], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55824, 56848, 57872, 52756, 53780, 54804], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55828, 56852, 57876, 30151955993, 51736, 52760], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 51740], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57888, 8626933285, 37001765, 37002789, 50724, 51748], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56872, 57896, 8593377837, 1099515149871, 49708, 50732], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51756, 52780, 53804, 54828, 55852, 56876], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48538860565, 86741249061, 35520757825, 35184995569, 34983809265, 34849731825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35251961165, 26595057997, 8794790233, 13173568873, 13089752425, 1100085581163], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13341266313, 13207118217, 8845046153, 1099901032847, 1099867479439, 1099833926031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018468255, 1099984914847, 1099934584223, 1099901030815, 1100035243443, 1099984912819], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [13374815673, 9012743609, 1099934511563, 1099934512587, 1099934579147, 4482965977], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099867400667, 1099867401691, 1099532001759, 56804, 57828, 56808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57832, 55788, 56812, 57836, 55792, 56816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57840, 54772, 55796, 56820, 57844, 4449409529], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 53756, 54780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55804, 56828, 57852, 53760, 54784, 55808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56832, 57856, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56836, 57860, 1099666072075, 1099666073099, 52744, 53768], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 52748, 53772], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 51728, 52752], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 25873834517], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57876, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55832, 56856, 57880, 50716, 51740, 52764], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 8626933281], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53778977, 1099565407779, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54816, 55840, 56864, 57888, 34396585509, 49700], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [56868, 57892, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 4298411565], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [3446317, 49708, 50732, 51756, 52780, 53804], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52766918681, 86690987053, 18408067145, 30890097901, 34933546221, 34782626029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31057660225, 22434376001, 13140017493, 1100052025715, 1100001695091, 1099968141683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934588275, 1099901034867, 13257383289, 13140012409, 1100186172795, 1100068798871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018468247, 1099984914839, 1099934584215, 13374816693, 8962412981, 1100001619387], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001620411, 1100001621435, 1100001687995, 57808, 4533296597, 1099884176855], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099884177879, 57812, 56792, 57816, 56796, 57820], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55776, 56800, 57824, 55780, 56804, 57828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54760, 55784, 56808, 57832, 54764, 55788], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56812, 57836, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 53752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 52732, 53756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 52736, 53760], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 52740, 53764], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 51720, 52744], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 57864, 51724], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [4415853073, 120887825, 1099632516627, 1099632517651, 50704, 51728], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56852, 57876, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 1099548704287, 49692], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [56860, 57884, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 49700], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56868, 57892, 21494983209, 48680, 49704, 50728], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [57896, 12888343085, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61222835229, 86657568817, 30755950825, 34816110825, 13475632361, 31040951589], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22384047397, 22132460837, 17451757913, 8845051225, 8794788185, 1099867479419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099833926011, 1099901030799, 1099867477391, 1099817146767, 8895374737, 1099984913819], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934583195, 1099884252571, 1100119060895, 1100119061919, 1100068731295, 1100052020639], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001690015, 8945634757, 8828262853, 57800, 57804, 56784], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57808, 56788, 57812, 55768, 56792, 57816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099850622431, 1099850623455, 1099850624479, 55772, 56796, 57820], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55776, 56800, 57824, 54756, 55780, 56804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57828, 54760, 55784, 56808, 57832, 53740], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54764, 55788, 56812, 57836, 53744, 54768], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55792, 56816, 57840, 52724, 53748, 54772], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55796, 56820, 57844, 52728, 53752, 54776], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55800, 56824, 57848, 52732, 53756, 54780], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55804, 56828, 57852, 17367791105, 8777927169, 4399077889], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099699626499, 51712, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56832, 57856, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55812, 56836, 57860, 51720, 52744, 53768], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 50700, 51724], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [30185510417, 50704, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55824, 56848, 57872, 49684, 50708, 51732], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55832, 56856, 57880, 4331968029, 1099582184991, 49692], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56860, 57884, 48672, 49696, 50720, 51744], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [1099548703271, 48676, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 20223529], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [20224553, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 48684], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [49708, 50732, 51756, 52780, 53804, 54828], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61222969377, 73839844405, 30605024509, 30437326077, 4835368189, 26779607337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26444135721, 22015088937, 13106462041, 8794787161, 1100018473307, 8828268929], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817147779, 1099783594371, 1099917806991, 1099884253583, 1099833922959, 1100051955091], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100035244435, 1100001691027, 1099951360403, 8928926125, 4583630253, 1100051951023], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099984843199, 1099968067007, 1099968133567, 57796, 57800, 13290929613], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8928857549, 56780, 57804, 56784, 57808, 55764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56788, 57812, 55768, 56792, 57816, 54748], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55772, 56796, 57820, 54752, 55776, 56800], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57824, 54756, 55780, 56804, 57828, 53736], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54760, 55784, 56808, 57832, 53740, 54764], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55788, 56812, 57836, 52720, 53744, 54768], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55792, 56816, 57840, 1099749959159, 1099749960183, 52724], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 52728], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 57848, 51708], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52732, 53756, 54780, 55804, 56828, 57852], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4399077889, 1099699626499, 51712, 52736, 53760, 54784], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55808, 56832, 57856, 51716, 52740, 53764], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 50696, 51720], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50700, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56844, 57868, 49680, 50704, 51728, 52752], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 1099548704279], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49684, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55828, 56852, 57876, 49688, 50712, 51736], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [25840280093, 70556189, 1099582184991, 49692, 50716, 51740], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [4348743201, 53777953, 48672, 49696, 50720, 51744], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [48676, 49700, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [54820, 55844, 56868, 57892, 48680, 49704], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [56872, 57896, 1099515147823, 47660, 48684, 49708], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 139 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65434184741, 56743930941, 26678947097, 26410649881, 21981537561, 21830614297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13223974169, 1099951363439, 1099917810031, 1099867479407, 1099833925999, 1100169395571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119064947, 1100119131507, 1100068800883, 1100018470259, 1099984916851, 8878597525], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100152615319, 1100135839127, 1100068731287, 9096628661, 8912082357, 8794710453], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57788, 57792, 56772, 57796, 56776, 57800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56780, 57804, 55760, 56784, 57808, 55764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56788, 57812, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099850624479, 54748, 55772, 56796, 57820, 54752], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55776, 56800, 57824, 53732, 54756, 55780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56804, 57828, 1099800289771, 1099800290795, 1099800291819, 53736], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54760, 55784, 56808, 57832, 52716, 53740], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54764, 55788, 56812, 57836, 52720, 53744], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 21713087989, 8828192245], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51704, 52728, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57848, 51708, 52732, 53756, 54780, 55804], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56828, 57852, 51712, 52736, 53760, 54784], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55808, 56832, 57856, 4449408517, 1099682848263, 1099548705287], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50692, 51716, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56836, 57860, 50696, 51720, 52744, 53768], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 50700, 51724], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [1099548704275, 49680, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 49684, 50708], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [57876, 49688, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 1099548703263, 48668], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55836, 56860, 57884, 48672, 49696, 50720], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [57888, 48676, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 47656], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [48680, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [54824, 55848, 56872, 57896, 3446317, 3447341], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [1099515147823, 47660, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65400698921, 43909363777, 26578352405, 22149305621, 21914430741, 17451762985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8878676265, 1100119131503, 1100068800879, 1100035247471, 1099984916847, 1099934586223], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884255603, 1099850702195, 1099800371571, 8861822337, 1100152617347, 1100102286723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100102353283, 8895305145, 4583629241, 1100001618363, 57784, 57788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57792, 1099951287751, 1099951288775, 1099934512583, 56772, 57796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56776, 57800, 55756, 56780, 57804, 55760], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56784, 57808, 54740, 55764, 56788, 57812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [17535564249, 8895303129, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54748, 55772, 56796, 57820, 53728, 54752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55776, 56800, 57824, 53732, 54756, 55780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56804, 57828, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57832, 52716, 53740, 54764, 55788, 56812], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57836, 52720, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57840, 51700, 52724, 53748, 54772, 55796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56820, 57844, 51704, 52728, 53752, 54776], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55800, 56824, 57848, 51708, 52732, 53756], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 1099699626499, 1099699627523], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [50688, 51712, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56832, 57856, 4399077893, 50692, 51716, 52740], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 50696], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [57864, 50700, 51724, 52748, 53772, 54796], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55820, 56844, 57868, 1099548704275, 49680, 50704], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [57872, 49684, 50708, 51732, 52756, 53780], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 49688, 50712], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [57880, 1099548703263, 48668, 49692, 50716, 51740], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [53778977, 1099565407779, 48672, 49696, 50720, 51744], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [4331965989, 4315190821, 48676, 49700, 50724, 51748], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [47656, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 3446317], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [1099515147823, 47660, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78101120045, 18307403849, 30806213869, 26377168109, 30437327085, 13123240265], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068802907, 1100018472283, 1099968141659, 1099934588251, 1099901034843, 8962483585], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828268929, 1100102286723, 1100068798855, 1100018468231, 1099968137607, 1099917806983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13425149345, 9012745633, 8878596513, 57784, 1099984843199, 1099968067007], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951356351, 57788, 56768, 57792, 56772, 57796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55752, 56776, 57800, 55756, 56780, 57804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55760, 56784, 57808, 54740, 55764, 56788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57812, 54744, 55768, 56792, 57816, 1099850624479], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54748, 55772, 56796, 57820, 53728, 54752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55776, 56800, 57824, 53732, 54756, 55780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56804, 57828, 1099800289771, 1099800290795, 1099800291819, 52712], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53736, 54760, 55784, 56808, 57832, 52716], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53740, 54764, 55788, 56812, 57836, 52720], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 51700], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51704, 52728, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57848, 51708, 52732, 53756, 54780, 55804], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56828, 57852, 50688, 51712, 52736, 53760], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 50692, 51716], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [4449408521, 154443273, 50696, 51720, 52744, 53768], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 49676, 50700], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [51724, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [57868, 1099548704275, 49680, 50704, 51728, 52752], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 49684], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56852, 57876, 49688, 50712, 51736, 52760], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 48668], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [55836, 56860, 57884, 48672, 49696, 50720], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [57888, 12921898533, 48676, 49700, 50724, 51748], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [47656, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 1099515147823], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [47660, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78067634225, 5489613901, 30755950825, 26293285097, 21897727209, 8794787153], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100001696083, 13140013417, 1100152619371, 1100135908715, 1100085578091, 1099850702191], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800371567, 1099917806983, 1099867476359, 1099833922951, 13324489105, 8962482577], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8811490705, 1100001622443, 1099984911787, 57780, 57784, 57788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56768, 57792, 56772, 57796, 1099934510539, 1099934511563], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099917735371, 55752, 56776, 57800, 55756, 56780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57804, 55760, 56784, 57808, 54740, 55764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56788, 57812, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53724, 54748, 55772, 56796, 57820, 53728], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54752, 55776, 56800, 57824, 53732, 54756], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55780, 56804, 57828, 52712, 53736, 54760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55784, 56808, 57832, 1099783512559, 1099783513583, 1099783514607], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52716, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52720, 53744, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51700, 52724, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57844, 51704, 52728, 53752, 54776, 55800], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56824, 57848, 8744374781, 204774909, 51708, 52732], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 57852, 50688], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51712, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57856, 1099548705287, 50692, 51716, 52740, 53764], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 50696, 51720], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50700, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56844, 57868, 49680, 50704, 51728, 52752], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 49684], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56852, 57876, 49688, 50712, 51736, 52760], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 48668], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [55836, 56860, 57884, 1099548703267, 48672, 49696], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [56864, 57888, 4331967013, 37001765, 48676, 49700], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [56868, 57892, 48680, 49704, 50728, 51752], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [1099515147823, 47660, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69528099893, 1228202061, 26410720505, 30437325049, 9063225593, 13140015445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811563349, 1100035249495, 1099884255599, 1099833924975, 1099766817143, 1099934583183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884252559, 1099833921935, 13190339989, 8794713493, 1100085508503, 1100018400663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018467223, 1099968136599, 57780, 57784, 56764, 57788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56768, 57792, 56772, 57796, 1099934510539, 1099934511563], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099934512587, 55752, 56776, 57800, 55756, 56780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57804, 55760, 56784, 57808, 54740, 55764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56788, 57812, 54744, 55768, 56792, 57816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53724, 54748, 55772, 56796, 57820, 4516519393], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [204776929, 1099833846243, 53728, 54752, 55776, 56800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57824, 53732, 54756, 55780, 56804, 57828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52712, 53736, 54760, 55784, 56808, 57832], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52716, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52720, 53744, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51700, 52724, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57844, 51704, 52728, 53752, 54776, 55800], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56824, 57848, 51708, 52732, 53756, 54780], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55804, 56828, 57852, 51712, 52736, 53760], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 50692, 51716], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [50696, 51720, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [56840, 57864, 50700, 51724, 52748, 53772], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 1099548704275, 49680], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [50704, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [56848, 57872, 42516, 49684, 50708, 51732], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [87334425, 37003801, 42520, 49688, 50712, 51736], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [42524, 48668, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 42528], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [1099548703267, 48672, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 41508], by decide +kernel⟩
private def p32 : P :=
  ⟨unpack [42532, 48676, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p33 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 41512], by decide +kernel⟩
private def p34 : P :=
  ⟨unpack [42536, 48680, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p35 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896, 41516], by decide +kernel⟩
private def p36 : P :=
  ⟨unpack [42540, 47660, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p37 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 57900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group2
