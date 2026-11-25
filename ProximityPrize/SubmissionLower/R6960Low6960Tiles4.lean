import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1023479817, 4613805065, 18757917709, 44344291345, 86942506017], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52851683389, 19093722203, 31292068097, 35319274781, 39329169693, 43456506141], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39463104865, 30890088801, 13190485369, 13291071897, 13207255449, 13106596249], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21847376321, 13257513409, 1099917941191, 1099917942215, 1099917943239, 1099867539923], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867540947, 1099867541971, 1099867608531, 4415994345, 1099766874603, 1099766875627], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4466321917, 4399215101, 21612558853, 1099632654859, 1099632655883, 53916185], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099565544987, 12921967133, 8627069469, 38658060837], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 137 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10083637259, 27449107469, 78234730521, 86926068785, 1580654669, 35520332025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35336054009, 39379503353, 34816241961, 13442143529, 35117734257, 13190476185], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13089816985, 1100102422939, 39161249185, 17619519913, 13257514409, 8912219561], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001760691, 1100001827251, 1099968273843, 1099834057163, 1099884315087, 1099884316111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884317135, 1099884318159, 30303086053, 17451812325, 1099783649767, 1099783650791], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4399214073, 1099699762683, 8710954501, 4382435845, 8643779093, 1099582321175], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57880, 38691618333, 37136925, 37137949, 57884, 25790015009], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [17200153121, 56864, 57888, 8593512997, 4298548773, 56868], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i54 : checks (tilesOf batches) 137 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27449107469, 61256187929, 86858890285, 18559127625, 35067755797, 34883281173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30538122517, 35403022633, 26762896681, 8845182345, 13257515413, 8912220565], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845180309, 1100085645719, 1100052092311, 1100018538903, 1100018605463, 1099985052055], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39211509153, 17569186241, 9012876737, 1099901094347, 1099901095371, 1099850759639], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850760663, 1099850761687, 1099783647719, 1099783648743, 1099783649767, 4466254321], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4415990257, 57864, 57868, 87468561, 1099599097363, 1099532065299], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56848, 57872, 56852, 57876, 25823569433, 1099532064283], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55832, 56856, 57880, 4332102173, 55836, 56860], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57884, 17200153121, 1099532063267, 54816, 55840, 56864], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57888, 34363166245, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
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
private theorem i49 : checks (tilesOf batches) 137 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [35972460561, 69762503709, 78269093941, 31124903193, 26662303001, 30688973081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26276639005, 21914635549, 1100119199115, 1100085645707, 1100052092299, 1100018538891], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018605451, 1099985052043, 39245066645, 13106590105, 1100102418843, 1100102419867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100085643675, 13274288561, 8895439281, 8811621809, 1099867535827, 1099867536851], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099766869483, 1099766870507, 1099766871531, 21662823921, 13056183793, 4432765437], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099682982399, 57852, 57856, 1099532065287, 56836, 57860], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56840, 57864, 1099532064271, 55820, 56844, 57868], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4382432785, 55824, 56848, 57872, 1099532063255, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 57876, 30118533657, 54808, 55832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56856, 57880, 8626998813, 4332100125, 1099532062239, 53788], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54812, 55836, 56860, 57884, 17200151073, 20358689], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888, 38658060837], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099515284007, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
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
private theorem i52 : checks (tilesOf batches) 137 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40250981397, 86741247013, 44077201473, 35302499569, 35067758833, 39161539825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13123376465, 13257518445, 13156924781, 13056265581, 1099951496591, 1099917943183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34966945173, 26377150869, 1100001758619, 1099968205211, 1099934651803, 1099901098395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13408438685, 13240736157, 8878664093, 1100001754547, 1100001755571, 1099984979379], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951425971, 1099901089227, 1099901090251, 17502076373, 1099783645671, 1099783646695], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099783647719, 57840, 4499806709, 4432765429, 57844, 1099532065275], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56824, 57848, 56828, 57852, 1099532064259, 55808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56832, 57856, 55812, 56836, 57860, 1099548840459], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 54796, 55820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56844, 57868, 1099548839443, 54800, 55824, 56848], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57872, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53912089, 53913113, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57880, 8626999837, 1099532061215, 52764, 53788, 54812], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55836, 56860, 57884, 52768, 53792, 54816], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55840, 56864, 57888, 17183374885, 1099515282983, 51748], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
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
private theorem i55 : checks (tilesOf batches) 137 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52834158617, 86724672557, 18441687113, 30890163445, 30705753333, 39044103413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35184986449, 22350556497, 17451892053, 1100068868475, 1100035315067, 1099984984443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951431035, 1099968274811, 13240737169, 8861887889, 8794847633, 1100052088219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018534811, 1099968204187, 13307774397, 8962545085, 1099917867463, 1099917868487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099917869511, 1099850755543, 1099850756567, 1099850757591, 1099548843495, 4432699881], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099766868459, 57832, 1099548842479, 57836, 56816, 57840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56820, 57844, 1099532064251, 55800, 56824, 57848], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55804, 56828, 57852, 1099532063235, 54784, 55808], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56832, 57856, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548839435, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [104243725, 1099615872527, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57868, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099532061207, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57876, 34413431321, 4348810777, 4332101145, 52760, 53784], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 50716, 51740], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56864, 57888, 21478272549, 12888409637, 3579429, 1099515282983], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52834292765, 86691186737, 5623962701, 35034204401, 30621936881, 21998521585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30940419413, 22266738005, 1100119199091, 1100068868467, 1100035315059, 1100001761651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13156855161, 8828403065, 1100119198075, 1099884387727, 1099850834319, 13358108053], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13207182741, 1099984977335, 1099968201143, 1099917870519, 1099951418815, 1099951419839], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099951420863, 1099951421887, 57824, 4499807717, 4432766437, 57828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532065259, 56808, 57832, 56812, 57836, 1099532064243], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55792, 56816, 57840, 55796, 56820, 57844], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548840443, 54776, 55800, 56824, 57848, 54780], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55804, 56828, 57852, 54784, 55808, 56832], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57856, 1099532062215, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57860, 8710884873, 4399143433, 1099632649739, 1099632650763, 53768], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 1099548838415, 52748], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 52752], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 57872, 21545448981], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53912089, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55832, 56856, 57880, 50716, 51740, 52764], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 50720], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57888, 4298545701, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57028730913, 73873463349, 1328996429, 30638643461, 30454167813, 9096845573], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26712564033, 22233185601, 21998376257, 13156923749, 8811628901, 1100068869479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901098371, 1099867544963, 1099817279887, 8845110673, 1099951425951, 1099917872543], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867541919, 1100035307947, 1100035308971, 1100001755563, 1099951424939, 8928990657], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4583694785, 1099934575043, 1099867532755, 1099867533779, 1099867534803, 1099532066267], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57816, 57820, 1099548842467, 56800, 57824, 56804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57828, 56808, 57832, 1099532064239, 55788, 56812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57836, 55792, 56816, 57840, 1099548840439, 54772], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55796, 56820, 57844, 17367924217, 8761217529, 54776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55800, 56824, 57848, 54780, 55804, 56828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57852, 1099532062211, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57856, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [121020937, 1099632649739, 51720, 52744, 53768, 54792], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55816, 56840, 57864, 1099532061199, 52748, 53772], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 52752, 53776], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 4332101141, 50708], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57876, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55832, 56856, 57880, 50716, 51740, 52764], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 20356641], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55840, 56864, 57888, 25773236773, 4298478117, 4298545701], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 137 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65467804709, 56760773693, 21964893469, 21813970205, 4717993245, 26729409825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233188641, 22015156513, 1100169528691, 1100135975283, 1100085644659, 1100035314035], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001760627, 1099951430003, 1099833990535, 1099834057095, 1100119194007, 1100119195031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100068864407, 8895439269, 1100052016551, 1100052083111, 1100052084135, 1099532066263], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57812, 13190400473, 4617247193, 57816, 1099548842463, 56796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57820, 56800, 57824, 56804, 57828, 1099532064235], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55784, 56808, 57832, 55788, 56812, 57836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [221618673, 1099733313011, 1099733314035, 1099548840435, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 57840, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 1099532062207, 53756], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 53760, 54784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55808, 56832, 57856, 52740, 53764, 54788], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55812, 56836, 57860, 21595713033, 13005850121, 51720], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099515283983, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57868, 50704, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55824, 56848, 57872, 50708, 51732, 52756], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 50712], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57880, 49692, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54812, 55836, 56860, 57884, 49696, 50720], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [57888, 4298479141, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [73906812969, 35437002817, 30890162433, 26427562241, 30470944001, 8828409157], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052095303, 13140079973, 1100219860327, 1100169529703, 1100119199079, 1100068868455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917874563, 1099867543939, 1099833990531, 9029654945, 8861885857, 4566987169], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100052085159, 1100052086183, 1100001755559, 17569184201, 13207178697, 1099532067275], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532066259, 57808, 57812, 1099548842459, 56792, 57816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56796, 57820, 56800, 57824, 4432766437, 1099783646695], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099783647719, 1099783648743, 1099532064231, 55780, 56804, 57828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55784, 56808, 57832, 1099548840431, 54764, 55788], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56812, 57836, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 1099548839419, 53752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 53756, 54780], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55804, 56828, 57852, 53760, 54784, 55808], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56832, 57856, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55812, 56836, 57860, 1099632649739, 1099632650763, 51720], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [4382432781, 1099515283983, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56844, 57868, 50704, 51728, 52752, 53776], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 50708, 51732], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [8643776025, 4348877337, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 49692, 50716], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [57884, 49696, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [54816, 55840, 56864, 57888, 3580453, 49700], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73873327149, 22619212869, 30823122173, 26343679229, 21931344125, 1100035316059], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099984985435, 1099951432027, 1100236636527, 1100186305903, 1100135975279, 1100085644655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035314031, 1099984983407, 8962549129, 8828334473, 1100169526667, 13358106037], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [9012876725, 8828330421, 1099917865415, 1099917866439, 1099917867463, 1099548844487], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548843471, 57808, 57812, 1099532065243, 56792, 57816], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56796, 57820, 1099548841443, 55776, 56800, 57824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099783646695, 55780, 56804, 57828, 55784, 56808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57832, 1099548840431, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [221618673, 1099733313011, 1099733314035, 54768, 55792, 56816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57840, 54772, 55796, 56820, 57844, 1099548839419], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 57848, 53756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54780, 55804, 56828, 57852, 53760, 54784], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55808, 56832, 57856, 51716, 52740, 53764], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54788, 55812, 56836, 57860, 51720, 52744], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 57864, 1099515283983], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50704, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56848, 57872, 50708, 51732, 52756, 53780], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 50712, 51736], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [4332033565, 4315323933, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 49696], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56864, 57888, 3579429, 49700, 50724, 51748], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78084476977, 5556853837, 30772793581, 30571606253, 17670000877, 1100068868455], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018537831, 1099984984423, 13173633385, 8828404073, 1100102421867, 1099833990527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834057087, 13374951833, 8962548121, 8811556249, 1100001755559, 1099951424935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901094311, 1100001753523, 1100001754547, 1099548843471, 57804, 1099867532755], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867533779, 1099867534803, 57808, 57812, 1099532065243, 56792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57816, 56796, 57820, 1099548841443, 55776, 56800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57824, 55780, 56804, 57828, 55784, 56808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57832, 1099548840431, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 4432765429, 1099716536823], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 1099548839419, 53752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 53756, 54780], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55804, 56828, 57852, 53760, 54784, 55808], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56832, 57856, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55812, 56836, 57860, 51720, 52744, 53768], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 1099515283983, 52748], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 8677331473], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [4382432785, 50704, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55824, 56848, 57872, 50708, 51732, 52756], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 53913113], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56856, 57880, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 49696], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56864, 57888, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69544942645, 1295441997, 26427563261, 26209532157, 13341480189, 8912288105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203083115, 1100152752491, 1100102421867, 1100052091243, 1099984983407, 1099951429999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901099375, 1099800502663, 9012878749, 8845109661, 1100085638559, 1099968199099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968200123, 1099934646715, 1099532066255, 57804, 57808, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57812, 1099532065243, 56792, 57816, 1099817200095, 1099817201119], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099817202143, 56796, 57820, 1099548841443, 55776, 56800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57824, 55780, 56804, 57828, 55784, 56808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57832, 1099548840431, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 54772, 55796], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56820, 57844, 1099548839419, 53752, 54776, 55800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56824, 57848, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57852, 53760, 54784, 55808, 56832, 57856], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4432764421, 137799173, 51716, 52740, 53764, 54788], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55812, 56836, 57860, 51720, 52744, 53768], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54792, 55816, 56840, 57864, 1099515283983, 52748], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 57868, 50704], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57872, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55828, 56852, 57876, 50712, 51736, 52760], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 50716], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [57884, 49696, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54816, 55840, 56864, 57888, 49700, 50724], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [57892], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 137 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group4
