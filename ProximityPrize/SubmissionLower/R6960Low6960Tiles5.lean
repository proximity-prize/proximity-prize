import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass5

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 1023479819, 4613805065, 18858646541, 56960823313, 86976194597], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [40067513409, 19093787737, 31275356417, 39681143073, 35336050977, 35118153001], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34950455593, 17418405269, 8828475797, 17468662201, 13089813945, 8694253009], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850830291, 1099850831315, 1099850832339, 1099850833363, 1099850834387, 21746777569], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17401550305, 4466390509, 4399283693, 1099733386735, 1099733387759, 1099733388783], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4432767489, 4416057857, 1099615944203, 1099615945227, 34447055373, 38691615257], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [12922033689, 8627136025, 1099548834331, 3650081, 3651105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10285029387, 27449107469, 73990094873, 86926067761, 5842066509, 35554017541], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31158592773, 39379567877, 34849860905, 17737175337, 39177951649, 13190475169], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106658721, 8778141089, 1099985050035, 17636361653, 13291133365, 13140142517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901164995, 1099867611587, 1099850829267, 1099850830291, 1099850831315, 1099817270747], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817271771, 1099817272795, 1099817273819, 1099733383663, 4449544693, 4399280629], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30152156685, 70758929, 1099582387731, 8627067417, 4332168729, 1099548910107], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [20426269, 38658054689, 1099515354659], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27449107469, 52834025497, 86875665449, 27132348485, 30923781397, 34967229717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833086741, 35235316049, 30839891281, 13156923785, 8828471693, 1100119266703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085713295, 1100052159887, 1100035383695, 39194797473, 13291066793, 13173695913], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8828401065, 1099884382667, 1099884383691, 1099884384715, 1099867603407, 1099867604431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17418257893, 1099766937063, 1099766938087, 1099766939111, 4466320881, 4416056817], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25857189389, 17267327501, 8677399053, 1099532132879, 70757905, 1099582386707], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099548909075, 57876, 1099548908059, 57880, 4315391517, 56860], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57884, 8593511969, 54816, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36022857745, 82513253405, 65484923961, 31259120889, 39413052665, 43473280249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21813971257, 1100320596283, 17586036089, 13240807801, 13156991353, 1100102488463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068935055, 1100035381647, 1100001828239, 39194800545, 21931259313, 13324619185], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934712255, 1099934713279, 1099934714303, 1099934715327, 1099850756563, 1099850823123], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850824147, 1099850825171, 8794840541, 4466321885, 1099548910079, 1099532131847], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [104311305, 1099615940107, 57864, 1099532130831, 56844, 57868], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4365655569, 70690321, 56848, 57872, 54804, 55828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56852, 57876, 30101821977, 54808, 55832, 56856], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57880, 12905254429, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57884, 21478406689, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44445350933, 86758090789, 39832632385, 31108262133, 35084601589, 39144762613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13106664797, 13291138413, 13156924781, 13089885549, 39278689661, 26461037949], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917942167, 1099884388759, 1100018601379, 1099985047971, 1099951494563, 1099901163939], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13408504229, 13240801701, 8878729637, 1099985042867, 1099985043891, 1099985044915], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099985045939, 1099850823123, 1099850824147, 1099733314031, 1099733315055, 1099733381615], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17367925233, 1099548910067, 1099548909051, 8694176253, 154576381, 57852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55808, 57856, 55812, 56836, 57860, 55816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56840, 57864, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 38708461077, 53780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 4332100121, 37134873], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 52764], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 17183441441], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52867778585, 86724672557, 18458529865, 30923783413, 34950454517, 34799534325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185051993, 26511371609, 13156925793, 1100102488447, 1100052157823, 1100018604415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985051007, 1099951497599, 13324688773, 13156920709, 1100169526663, 1100035375527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100035376551, 1100018600359, 1099968269735, 13257509317, 8912280005, 1099884309963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884310987, 1099884377547, 1099884378571, 1099532132843, 204908017, 1099716536819], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 57840, 1099532131831, 57844, 55800, 57848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55804, 56828, 57852, 54784, 55808, 56832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57856, 54788, 55812, 56836, 57860, 54792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55816, 56840, 57864, 21562224141, 12972361229, 53772], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 53776, 54800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55824, 56848, 57872, 4348877333, 53912085, 52756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 52760], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 52764], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 34363165217], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4298544673, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52867912733, 86691186737, 5623962701, 35067824369, 30621936881, 21998521585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30890153309, 22266803549, 1100169596275, 1100119265651, 1100085712243, 1100035381619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190475129, 8828403065, 1100169595259, 1099884387727, 1099850834319, 13374950813], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13207248285, 1099968265655, 1099968266679, 1099968267703, 1099901087175, 1099901088199], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901154759, 1099901155783, 1099548910051, 56808, 4499873261, 4399212013], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56812, 57836, 55792, 56816, 57840, 55796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56820, 57844, 55800, 56824, 57848, 54780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55804, 56828, 57852, 54784, 55808, 56832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57856, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099615872523, 1099615939083, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57864, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8643841557, 4348877333, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56852, 57876, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55832, 56856, 57880, 21495117341, 51740, 52764], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 57884, 3580449], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65501290529, 69595340857, 30571602189, 26159268109, 4818722061, 31007596837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26528219429, 26276633893, 8828404077, 1100169596271, 1100119265647, 1100068935023], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035381615, 8794847625, 1099867610511, 1099834057103, 13190471073, 8811621793], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001822123, 1099951491499, 1099934710207, 1099934711231, 1099934712255, 1099817201115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817202139, 1099817268699, 17451811293, 8861947357, 1099532132831, 56804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57828, 56808, 57832, 4449542637, 1099733314031, 55788], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56812, 57836, 55792, 56816, 57840, 54772], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55796, 56820, 57844, 54776, 55800, 56824], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57848, 54780, 55804, 56828, 57852, 53760], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 53764, 54788], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55812, 56836, 57860, 30168932873, 53768, 54792], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55816, 56840, 57864, 52748, 53772, 54796], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55820, 56844, 57868, 52752, 53776, 54800], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55824, 56848, 57872, 53912085, 1099565540887, 51732], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [57880, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56860, 57884, 17183441441, 4298544673, 3579425, 50720], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 136 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [73957141541, 48254792765, 26830073097, 30756079881, 26293414153, 17502225713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8912361777, 1100169594243, 1100119263619, 1100068932995, 1100018602371, 1099968271747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934718339, 1099901164931, 1099850834307, 13156919689, 1100152748427, 1100152749451], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100152816011, 13358172593, 8996166065, 8828396977, 1099867533775, 1099867600335], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57812, 57816, 1099515355615, 56800, 57824, 56804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57828, 55784, 56808, 57832, 1099733313007, 1099733314031], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099733315055, 55788, 56812, 57836, 54768, 55792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56816, 57840, 54772, 55796, 56820, 57844], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54776, 55800, 56824, 57848, 53756, 54780], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55804, 56828, 57852, 53760, 54784, 55808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56832, 57856, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57860, 25873968649, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [56840, 57864, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56844, 57868, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56848, 57872, 4348877333, 53912085, 51732, 52756], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 51736], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 57880], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57884, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55840, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65451161641, 43959826497, 26612037921, 22166213921, 26192817441, 13207259445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8895584565, 1099917941123, 1099884387715, 1099850834307, 1100085709191, 1100035378567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985047943, 1099951494535, 8895507849, 1100152748427, 1100152749451, 1100152816011], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100119262603, 8962610633, 4600537545, 4483099081, 1099833979351, 1099834045911], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57812, 57816, 56796, 57820, 56800, 57824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55780, 56804, 57828, 55784, 56808, 57832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [21679667693, 8811614701, 55788, 56812, 57836, 54768], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55792, 56816, 57840, 54772, 55796, 56820], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57844, 1099682982395, 1099683048955, 53752, 54776, 55800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56824, 57848, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57852, 53760, 54784, 55808, 56832, 57856], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52744, 53768, 54792, 55816, 56840, 57864], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 57868], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57872, 53912085, 53913109, 51732, 52756, 53780], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54804, 55828, 56852, 57876, 51736, 52760], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 57880, 50716], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [57884, 21478406689, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54816, 55840, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73890169901, 22652832837, 30839964929, 26360521985, 26176045313, 1100001828195], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968274787, 8845181285, 1100169596263, 1100119265639, 1100068935015, 1100035381607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979391889, 8828400017, 1100119195027, 1100035375527, 1100001822119, 1099951491495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17552475581, 8962611645, 1099867533775, 1099867600335, 1099867601359, 57808], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57812, 56792, 57816, 56796, 57820, 56800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57824, 55780, 56804, 57828, 55784, 56808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57832, 54764, 55788, 56812, 57836, 204908017], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099716536819, 1099716603379, 54768, 55792, 56816, 57840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 53752, 54776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55800, 56824, 57848, 53756, 54780, 55804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56828, 57852, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57856, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57860, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57864, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57868, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56848, 57872, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55828, 56852, 57876, 12922029593, 8627066393, 37134873], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57880, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55836, 56860, 57884, 50720, 51744, 52768], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82362732593, 1295441997, 30823190761, 30588383465, 17686778089, 1100119265639], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100068935015, 1100035381607, 1099985050983, 13207253353, 1100270190955, 8828470633], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817279879, 13324620193, 8962613665, 8811621793, 1100001822119, 1099951491495], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901160871, 1099951487419, 1099951488443, 57808, 57812, 1099817201115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099817202139, 1099817268699, 56792, 57816, 56796, 57820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56800, 57824, 55780, 56804, 57828, 55784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56808, 57832, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 54772, 55796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56820, 57844, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57848, 4399211005, 1099666205183, 53756, 54780, 55804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56828, 57852, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57856, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [57860, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57864, 8677397005, 4382432781, 52748, 53772, 54796], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55820, 56844, 57868, 51728, 52752, 53776], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54800, 55824, 56848, 57872, 51732, 52756], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 57876, 37201433], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51736, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [57880, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55836, 56860, 57884, 1099515281955, 50720, 51744], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69561785397, 1278664781, 26444406017, 26226374913, 13358322945, 8878733681], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100219925875, 1100169595251, 1100119264627, 1100068934003, 1100001826167, 1099968272759], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917942135, 1099817279875, 9012944293, 8845175205, 1100035306919, 1099951487419], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951488443, 1099951489467, 57804, 57808, 57812, 56792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57816, 56796, 57820, 56800, 57824, 1099766868455], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099766869479, 1099766936039, 55780, 56804, 57828, 55784], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56808, 57832, 54764, 55788, 56812, 57836], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54768, 55792, 56816, 57840, 54772, 55796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56820, 57844, 53752, 54776, 55800, 56824], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57848, 53756, 54780, 55804, 56828, 57852], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 57856, 52740], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 57860, 52744], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 57864, 4382432781], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [87467533, 52748, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [57868, 51728, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56848, 57872, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55828, 56852, 57876, 51736, 52760, 53784], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 50716, 51740], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56864, 57888], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group5
