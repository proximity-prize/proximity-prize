import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass3

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 1023479817, 4613805065, 18640411661, 86606032913, 86993110061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10170521673, 18976216155, 35721326781, 44026451133, 65132462269, 31292002561], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34765914421, 26377159017, 26209459561, 26092091753, 13056267673, 8811559353], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984913851, 8744520121, 30504277441, 21914416577, 1099934651847, 1099934652871], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099934653895, 1099934654919, 13140073941, 8778001877, 1099817208291, 1099817209315], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099817210339, 1099750029811, 1099750030835, 1099750097395, 13072895485, 38808924677], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [154512901, 1099666141703, 1099666142727, 8660557333, 87403029, 34362954281], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4298481193, 4298483241], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i51 : checks (tilesOf batches) 138 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9899022347, 27381933069, 82462523417, 86926069809, 31409848553, 39597400297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47885486313, 34782689577, 4919319849, 35318864197, 17736894853, 17585970565], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17468600709, 35000434065, 13072975249, 1100135978387, 1100102424979, 1099951359427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951425987, 1099951427011, 1099951428035, 1099867545027, 1099833991619, 26158981581], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17569185229, 8727671245, 1099901025743, 1099901026767, 8794775017, 4466256361], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099750027763, 1099750028787, 1099750029811, 8710885901, 57872, 87403029], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099599031831, 57876, 56856, 57880, 4348812829, 53847581], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56860, 57884, 55840, 56864, 57888, 55844], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56868, 57892, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i54 : checks (tilesOf batches) 138 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27381933069, 57011486745, 86858823721, 22820473925, 35084466449, 39161470225], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30521279761, 35302293813, 26712565045, 8845116801, 1100135977355, 1100102423947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068870539, 1100035317131, 1100001763723, 13291003277, 13190409613, 8845114765], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [35000296849, 17569186241, 8962479553, 1099951425987, 1099934649795, 1099901025743], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901026767, 1099901093327, 1099850690011, 1099850691035, 1099850692059, 1099850693083], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4466254321, 1099750025715, 57856, 57860, 56840, 57864], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56844, 57868, 55824, 56848, 57872, 55828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56852, 57876, 34430208537, 21545381401, 54808, 55832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56856, 57880, 8627000861, 53846557, 53847581, 54812], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55836, 56860, 57884, 12921898529, 53792, 54816], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55840, 56864, 57888, 53796, 54820, 55844], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56868, 57892, 4298479145, 3513897, 52776, 53800], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
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
private theorem i49 : checks (tilesOf batches) 138 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40066035729, 78251841569, 65451303993, 26980866309, 30890095877, 34933544197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21914564913, 17535717681, 35184849253, 30806136165, 1100085645707, 1100035315083], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001761675, 1099968208267, 1099951432075, 13324555665, 13173564817, 8845112721], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100102353311, 1100068799903, 1100035246495, 1100035313055, 17569117645, 13223889357], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884246483, 1099884247507, 1099884248531, 4499809753, 1099850690011, 1099850691035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57844, 56824, 57848, 4483029501, 4399145469, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57852, 55808, 56832, 57856, 55812, 56836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57860, 54792, 55816, 56840, 57864, 1099632585231], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 54800, 55824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56848, 57872, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57876, 30135244313, 70623769, 1099582252571, 53784, 54808], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55832, 56856, 57880, 1099531995679, 52764, 53788], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54812, 55836, 56860, 57884, 8626932257, 4332033569], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099531994663, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56868, 57892, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
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
private theorem i52 : checks (tilesOf batches) 138 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48538860565, 86741249061, 35537600577, 31041088753, 39262063857, 34849731825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35251961165, 26645455181, 8811632989, 13207188841, 13089752425, 8794854761], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13458771333, 13274226053, 13156855173, 1099850768791, 1100018468255, 1099984914847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984981407, 1099951427999, 1099917874591, 1099884321183, 1099850767775, 1099984911803], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951358395, 1099917798859, 1099917799883, 1099917800907, 1099917801931, 17468521949], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4516584933, 1099800356327, 1099800357351, 57832, 57836, 56816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57840, 56820, 57844, 55800, 56824, 57848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55804, 56828, 57852, 54784, 55808, 56832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57856, 54788, 55812, 56836, 57860, 53768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 53772, 54796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55820, 56844, 57868, 8677331473, 1099548772883, 52752], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 52756], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 1099548771867], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53845533, 53846557, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55836, 56860, 57884, 25806725665, 51744, 52768], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 34379808293], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [12905119269, 8610221605, 1099531993639, 50724, 51748, 52772], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892, 3512873], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
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
private theorem i55 : checks (tilesOf batches) 138 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52800538649, 86707829805, 18441687113, 30906940657, 34916769009, 34782691569], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31007394121, 22400821577, 13156860249, 13291003257, 13173632377, 8828337529], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068868475, 1100018537851, 1099984984443, 1099951431035, 1099917877627, 1099951360415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951426975, 1099984911799, 1099934581175, 1099901027767, 13341327805, 8979255741], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951353283, 1099951354307, 1099951355331, 1099951356355, 4533362141, 1099833910751], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099833911775, 57820, 57824, 56804, 57828, 56808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57832, 55788, 56812, 57836, 55792, 56816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57840, 54772, 55796, 56820, 57844, 54776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55800, 56824, 57848, 54780, 55804, 56828], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57852, 53760, 54784, 55808, 56832, 57856], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 1099548772875], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099531994647, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56852, 57876, 70622745, 1099582251547, 51736, 52760], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 4348809757], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [4332034589, 1099548770847, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54812, 55836, 56860, 57884, 50720, 51744], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [56868, 57892, 21478271529, 3512873, 1099515215403, 49704], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61256455197, 78168363057, 5590342733, 30688907521, 26276573441, 21897792769], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31057794349, 26561639725, 1100102356331, 1100052025707, 1100068869483, 1100018538859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895443325, 1100203015551, 1100152684927, 1100102354303, 1100052023679, 1099867544967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099833991559, 13291000217, 8912150937, 8811556249, 1099917801931, 1099884244435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884245459, 1099884246483, 57812, 57816, 56796, 57820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56800, 57824, 55780, 56804, 57828, 4432699881], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099783580139, 55784, 56808, 57832, 17434899949, 8845036013], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548774895, 55788, 56812, 57836, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 57840, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099531996667, 53752, 54776, 55800, 56824, 57848], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4483028477, 4399144445, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57852, 1099548772867, 52736, 53760, 54784, 55808], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56832, 57856, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56836, 57860, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56840, 57864, 1099632584207, 1099548771855, 51724, 52748], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 51728], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57876, 70622745, 1099582251547, 1099548770843, 50712, 51736], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [30118467101, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55836, 56860, 57884, 50720, 51744, 52768], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 1099531992615], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [55844, 56868, 57892, 49704, 50728, 51752], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57028730913, 78101256245, 30672132341, 30487656693, 9130334453, 26712564033], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22199565633, 17770452289, 13156858205, 8811563357, 1100085646687, 1099934652795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901099387, 1099867545979, 8912218505, 1100186236299, 1099934583191, 1099934649751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901096343, 1100085574051, 1100035243427, 1099984912803, 1099934582179, 8828261841], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4516585937, 57808, 57812, 1099850688987, 1099850690011, 1099850691035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56792, 57816, 56796, 57820, 55776, 56800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57824, 55780, 56804, 57828, 54760, 55784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56808, 57832, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [17384635889, 8761151985, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 53752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 1099548772863, 52732], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 57852, 52736], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 57856, 52740], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 1099649360395], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099649361419, 1099548771851, 51720, 52744, 53768, 54792], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55816, 56840, 57864, 120954381, 51724, 52748], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 51728], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [1099548770839, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55828, 56852, 57876, 50712, 51736, 52760], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 4348809757], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53844509, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55836, 56860, 57884, 1099548769827, 49696, 50720], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [57888, 25789948453, 12905119269, 8610221605, 49700, 50724], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [57892, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 138 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65434184741, 56743930941, 26712567065, 22266743065, 22048710937, 21881010457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17485386009, 1100035248487, 1100035315047, 1100001761639, 1099951431015, 1099917877607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100236568959, 1100169461119, 1100119130495, 1100068799871, 1100018469247, 1099984915839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8861819301, 1100068793767, 1100068794791, 1100068795815, 57800, 57804], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56784, 57808, 56788, 57812, 13156780505, 4566850009], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56792, 57816, 55772, 56796, 57820, 55776], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56800, 57824, 1099548774887, 54756, 55780, 56804], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57828, 4432699881, 1099783580139, 54760, 55784, 56808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57832, 54764, 55788, 56812, 57836, 1099531996659], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 53748], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 1099548772859, 52728], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 57848, 21662756349], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13056116221, 52732, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57852, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57856, 1099548771847, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55812, 56836, 57860, 51720, 52744, 53768], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 1099632583183, 1099632584207], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51724, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57868, 1099548770835, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 50708, 51732], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [56856, 57880, 4348810781, 53845533, 1099548769823, 49692], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [56860, 57884, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 49700], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [56868, 57892, 8593376809, 4298478121, 48680, 49704], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [73906812969, 35403382849, 30890162433, 26393942273, 26209465601, 13089755453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068872511, 8895444333, 1100186239343, 1100135908719, 1100085578095, 1100035247471], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018536819, 1099968206195, 1099934652787, 1099901099379, 13207116185, 8845109657], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984909755, 1099984910779, 1099917802939, 57796, 17585895881, 8996031945], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57800, 57804, 56784, 57808, 56788, 57812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099850688987, 1099850690011, 1099850691035, 55768, 56792, 57816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55772, 56796, 57820, 54752, 55776, 56800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57824, 54756, 55780, 56804, 57828, 4550138345], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4432699881, 54760, 55784, 56808, 57832, 1099548773871], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53740, 54764, 55788, 56812, 57836, 53744], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 53748, 54772], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55796, 56820, 57844, 1099548772859, 52728, 53752], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 52732, 53756], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 52736, 53760], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 1099548771847, 51716], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57864, 1099632583183, 1099632584207, 51724, 52748, 53772], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 1099548770835, 50704], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [57872, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55828, 56852, 57876, 50712, 51736, 52760], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 1099548769823], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [49692, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [55836, 56860, 57884, 49696, 50720, 51744], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [55844, 56868, 57892, 3512873, 3513897, 48680], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73873327149, 22585592901, 26595198205, 26377232637, 26192755965, 1100052093267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018539859, 1099984986451, 8861891941, 1100119132519, 1100068801895, 1100018471271], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018537831, 8945705361, 8845110673, 1100152682899, 1099984911787, 1099934581163], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884250539, 13307774405, 8895370693, 57796, 57800, 56780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57804, 1099884244435, 1099884245459, 1099884246483, 56784, 57808], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55764, 56788, 57812, 55768, 56792, 57816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55772, 56796, 57820, 1099548774883, 54752, 55776], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56800, 57824, 54756, 55780, 56804, 57828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4432699881, 1099783580139, 54760, 55784, 56808, 57832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548773871, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 53748], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 1099548772859, 52728], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 57848, 52732], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 57852, 52736], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 57856, 1099548771847], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51716, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57860, 51720, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56840, 57864, 120955405, 1099632584207, 51724, 52748], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 4399142417], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [104177169, 1099548770835, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 50708, 51732], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56856, 57880, 1099548769823, 49692, 50716, 51740], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [55840, 56864, 57888, 49700, 50724, 51748], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [48680, 49704, 50728, 51752, 52776, 53800], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73839841329, 9801422921, 30722461945, 26259796217, 21864238329, 1100119133531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068802907, 1100068869467, 1099934652783, 1099901099375, 1099850768751, 13140078961], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100169462131, 1100119131507, 1100068800883, 13324554649, 8928928153, 8811556249], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018465203, 1099968134579, 57792, 57796, 57800, 56780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57804, 1099884244435, 1099884245459, 1099884246483, 56784, 57808], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55764, 56788, 57812, 55768, 56792, 57816], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55772, 56796, 57820, 1099548774883, 54752, 55776], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56800, 57824, 54756, 55780, 56804, 57828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54760, 55784, 56808, 57832, 4432699885, 1099766802927], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099531996655, 53740, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53744, 54768, 55792, 56816, 57840, 52724], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 57844, 1099548772859], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52728, 53752, 54776, 55800, 56824, 57848], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52732, 53756, 54780, 55804, 56828, 57852], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52736, 53760, 54784, 55808, 56832, 57856], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [8710820357, 4399144453, 1099548771847, 51716, 52740, 53764], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 51720, 52744], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 57864, 51724], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [1099615806995, 1099548770835, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 50708, 51732], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56856, 57880, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 37068321], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [37069345, 1099531992611, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 8610222629], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55844, 56868, 57892, 48680, 49704, 50728], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69528099893, 1261822029, 26410720505, 30437325049, 9063225593, 13173635413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811563349, 1100085646679, 1099934652783, 1099884322159, 1099783659903, 1099951360399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951426959, 1099901096335, 13190339989, 8828333461, 1100102351263, 1100052020639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984912799, 1099934582175, 57792, 57796, 56776, 57800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56780, 57804, 1099884244435, 1099884245459, 1099884246483, 56784], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57808, 55764, 56788, 57812, 55768, 56792], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57816, 55772, 56796, 57820, 4550139361, 4432700897], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54752, 55776, 56800, 57824, 54756, 55780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56804, 57828, 54760, 55784, 56808, 57832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53740, 54764, 55788, 56812, 57836, 53744], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 53748, 54772], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55796, 56820, 57844, 1099548772859, 52728, 53752], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 52732, 53756], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 52736, 53760], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 104179205, 1099666139655], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099548771847, 51716, 52740, 53764, 54788, 55812], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56836, 57860, 51720, 52744, 53768, 54792], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55816, 56840, 57864, 51724, 52748, 53772], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 1099548770835, 50704], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [57872, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55828, 56852, 57876, 50712, 51736, 52760], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 49692], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [56860, 57884, 37068321, 37069345, 42528, 1099548769827], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [55840, 56864, 57888, 42532, 49700, 50724], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [57892, 42536, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((3 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group3
