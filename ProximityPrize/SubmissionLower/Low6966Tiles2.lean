import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass2
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 1040257033, 4613805065, 18573237261, 86622810129, 86993044525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [5925820489, 18892264539, 31610843329, 35688108225, 56626279617, 31325556997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34849729845, 13492408629, 22216340865, 22015085953, 21864162689, 13106527661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100068801967, 1099951362507, 1099951363531, 1099917810131, 1099917811155, 8811488737], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4533367265, 1099850693091, 1099833916903, 1099833917927, 1099833918951, 1099833919975], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34564362753, 13072895493, 8744377861, 4365593113, 1099599032863, 1099599033887], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4315192877, 4315260461, 20295213], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i51 : checks (tilesOf batches) 140 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [9731184651, 27331535885, 86707093529, 78386402357, 31493669085, 39647666397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52197230813, 35402553629, 30454103353, 1100437904699, 22015084925, 17636303229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21729949053, 35084254597, 8794787225, 1100068805019, 8794781117, 1100001690047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001691071, 1100001692095, 26192536013, 17602674125, 1099934584271, 1099917808079], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884254671, 4533297645, 4449413613, 1099800359407, 1099783583219, 1099783584243], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099783585267, 8794706433, 4499742209, 120957461, 1099632586263, 34463554073], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532000795, 1099531999779, 56864, 56868, 37070377, 1099531998763], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55848, 56872, 55852, 56876, 1099515220531, 54832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i54 : checks (tilesOf batches) 140 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23305004045, 52783496213, 86841913385, 27132216389, 30973980941, 30755950861], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39127920909, 35302227265, 26729275713, 13223899521, 13140083073, 1100119134607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085581199, 1100052027791, 1100018474383, 13257380277, 13140009397, 1099984912835], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984913859, 1099968137667, 1099934584259, 39110780357, 1099901022679, 1099901023703], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901024727, 1099901025751, 17468456425, 4466188789, 1099766737399, 1099766803959], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532000779, 8727597585, 4399078929, 1099531999763, 56848, 56852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099531998747, 55832, 56856, 55836, 56860, 70624801], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 30118399525, 53796], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54820, 55844, 56868, 21511761449, 52776, 53800], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54824, 55848, 56872, 20225581, 20292141, 52780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 12888344113, 51760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52784, 53808, 54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
private theorem i49 : checks (tilesOf batches) 140 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40099590161, 78251776033, 61206602809, 27031197957, 30940427525, 30756017413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26125579581, 13291082045, 35184849261, 30822913389, 8845047189, 1100169462167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100135908759, 1100102355351, 1100068801943, 1099968139683, 1099934586275, 1099901032867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867479459, 9029522861, 8928928173, 8811490733, 1099901024727, 1099901025751], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17552340441, 13173492185, 1099833847271, 1099833913831, 1099833914855, 1099548777979], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099716403715, 1099716404739, 1099716405763, 1099548776963, 56836, 54792], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56840, 54796, 55820, 56844, 53776, 54800], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 56848, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4382300697, 53784, 54808, 55832, 56856, 52764], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 8660486689, 4365522465], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 30118401573], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [56876, 3448369, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
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
private theorem i52 : checks (tilesOf batches) 140 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44394888213, 86741182501, 35554311233, 31091353841, 39295551729, 39144698097], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119136611, 1100085583203, 17468535145, 13123306857, 8794789225, 35151297905], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26544791921, 17653008781, 13274226061, 8912153997, 1099901031839, 1100035245479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099984914855, 1099951361447, 1099917808039, 1100052019635, 1100052020659, 1100035244467], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867401695, 1099867468255, 1099867469279, 13190266345, 4482964973, 1099800290799], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099800291823, 1099548777967, 55796, 1099531999739, 56824, 54780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56828, 8794705409, 4466186753, 54784, 55808, 56832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54788, 55812, 56836, 53768, 54792, 55816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56840, 53772, 54796, 55820, 56844, 52752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 52756, 53780], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54804, 55828, 56852, 51736, 52760, 53784], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54808, 55832, 56856, 1099598963231, 51740, 52764], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 51744, 52768], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 50724, 51748], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 50728], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [25789948461, 20224557, 20225581, 50732, 51756, 52780], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 34363031089, 49712], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19]
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
private theorem i55 : checks (tilesOf batches) 140 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52834093081, 86707764269, 14196985929, 30906875121, 34950323441, 30554767601], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31007394129, 22417598801, 13123305833, 13307780481, 13156789633, 1100202950019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001694087, 1099968140679, 1099934587271, 1099901033863, 1100052021671, 1100001691047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951360423, 1099917807015, 13374816701, 8979190205, 1099968064967, 1099968065991], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099968132551, 1099968133575, 1099532000743, 4499742185, 1099817068011, 1099817069035], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55788, 56812, 55792, 56816, 54772, 55796], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56820, 54776, 55800, 56824, 53756, 54780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55804, 56828, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 52744, 53768], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54792, 55816, 56840, 52748, 53772, 54796], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55820, 56844, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55824, 56848, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55828, 56852, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55832, 56856, 4382298653, 87333405, 87334429, 1099598963231], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56860, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55840, 56864, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54820, 55844, 56868, 1099548704299, 49704, 50728], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [49708, 50732, 51756, 52780, 53804, 54828], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [55852, 56876, 49712, 50736, 51760, 52784], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53808, 54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52834227229, 86674278449, 1362418765, 35050916077, 30621805805, 17736977645], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30940353877, 22266672469, 13190344053, 8828271989, 1100135909751, 1100085579127], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052025719, 1100001695095, 1099968141687, 13374819733, 9029590421, 8878598549], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800370583, 1100018466227, 1099968135603, 1099917804979, 1099984909763, 1099984910787], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099867400671, 1099867401695, 1099867468255, 1099532000735, 55780, 56804], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55784, 56808, 54764, 55788, 56812, 54768], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55792, 56816, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54776, 55800, 56824, 53756, 54780, 55804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56828, 204774913, 1099716403715, 1099716404739, 52736, 53760], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [54784, 55808, 56832, 52740, 53764, 54788], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55812, 56836, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56840, 8744373773, 4399077901, 51724, 52748, 53772], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54796, 55820, 56844, 51728, 52752, 53776], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54800, 55824, 56848, 17300682261, 8710818325, 50708], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [56856, 50716, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55836, 56860, 49696, 50720, 51744, 52768], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 49700, 50724], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [30101624361, 37001769, 49704, 50728, 51752, 52776], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [53800, 54824, 55848, 56872, 48684, 49708], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56876, 48688, 49712, 50736, 51760, 52784], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53808, 54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57028665377, 73873397813, 26427496709, 26243020037, 13391745285, 26729275713], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22249897281, 21998310721, 8861824377, 1100186239355, 1100135908731, 1100102355323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052024699, 1099968139651, 1099934586243, 1099884255619, 1099850702211, 1100102282663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100102283687, 1100001686975, 1100001687999, 1099968134591, 8945702337, 4600406465], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099984841155, 56788, 56792, 55772, 1099515223519, 55776], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56800, 55780, 56804, 54760, 55784, 56808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54764, 55788, 56812, 53744, 54768, 55792], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56816, 53748, 54772, 55796, 56820, 53752], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54776, 55800, 56824, 13106380285, 8811482621, 52732], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 52736, 53760], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54784, 55808, 56832, 52740, 53764, 54788], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55812, 56836, 51720, 52744, 53768, 54792], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55816, 56840, 1099666072079, 1099666073103, 51724, 52748], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 50704, 51728], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 50708], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [4348746265, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55832, 56856, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 49696, 50720], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [55844, 56868, 25806725673, 37001769, 37002793, 49704], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56872, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 48688, 49712], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65467739173, 52516072509, 26729344289, 26427427105, 21981537569, 17569201449], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13223973161, 1099968139647, 1099934586239, 1099884255615, 1099850702207, 1100169461131], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100119130507, 1100068799883, 1100018469259, 1099968138635, 8878597533, 1100135838111], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100135839135, 1100085508511, 13257378241, 8895371713, 56784, 56788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55768, 56792, 55772, 56796, 55776, 56800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099833845223, 1099833846247, 1099833847271, 54756, 55780, 56804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54760, 55784, 56808, 53740, 54764, 55788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56812, 53744, 54768, 55792, 56816, 53748], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54772, 55796, 56820, 52728, 53752, 54776], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55800, 56824, 52732, 53756, 54780, 55804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56828, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51716, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [21645979145, 13056116233, 51720, 52744, 53768, 54792], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [55816, 56840, 4399077901, 1099666072079, 51724, 52748], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 50704, 51728], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 50708], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56856, 4382299677, 49692, 50716, 51740, 52764], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 49696, 50720], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55844, 56868, 37002793, 1099548703275, 48680, 49704], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [56872, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 48688, 49712], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [73906747433, 31175458881, 30890096897, 26427496705, 26243020033, 8828342605], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035251535, 8878601589, 1100186239351, 1100135908727, 1100085578103, 1100035247479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099917808011, 1099867477387, 1099817146763, 9029589409, 8861820321, 1100119060899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100001686975, 1100001687999, 1099951357375, 17619450313, 9012743625, 56780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56784, 55764, 56788, 55768, 56792, 55772], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56796, 54752, 55776, 56800, 1099833845223, 1099833846247], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099833847271, 54756, 55780, 56804, 54760, 55784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56808, 53740, 54764, 55788, 56812, 53744], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54768, 55792, 56816, 52724, 53748, 54772], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55796, 56820, 52728, 53752, 54776, 55800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56824, 52732, 53756, 54780, 55804, 56828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [51712, 52736, 53760, 54784, 55808, 56832], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51716, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [4399077901, 1099666072079, 50700, 51724, 52748, 53772], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [54796, 55820, 56844, 50704, 51728, 52752], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 50708, 51732], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 49688], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [50712, 51736, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [56856, 49692, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [54812, 55836, 56860, 49696, 50720, 51744], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [52768, 53792, 54816, 55840, 56864, 49700], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [56868, 37001769, 37002793, 48680, 49704, 50728], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [48684, 49708, 50732, 51756, 52780, 53804], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [54828, 55852, 56876, 8593378865, 48688, 49712], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73873261613, 18391288901, 30823056637, 30571472125, 26142360829, 13089752409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100001695083, 1099951364459, 1099901033835, 13240673657, 8861824377, 1100169462139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035245455, 1099984914831, 1099934584207, 1099884253583, 13391594933, 9012811189], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8845042101, 1100001686975, 1100001687999, 1099951357375, 56776, 56780], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099917733331, 1099917734355, 56784, 55764, 56788, 55768], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56792, 55772, 56796, 54752, 55776, 56800], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54756, 55780, 56804, 53736, 54760, 55784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56808, 53740, 54764, 55788, 56812, 53744], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54768, 55792, 56816, 1099766735351, 1099766736375, 1099766737399], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 52728], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 52732, 53756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54780, 55804, 56828, 51712, 52736, 53760], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54784, 55808, 56832, 51716, 52740, 53764], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54788, 55812, 56836, 51720, 52744, 53768], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [54792, 55816, 56840, 50700, 51724, 52748], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 50704, 51728], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 50708], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51732, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [49688, 50712, 51736, 52760, 53784, 54808], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [55832, 56856, 4382299677, 87334429, 49692, 50716], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [55840, 56864, 49700, 50724, 51748, 52772], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 48680, 49704], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56872, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 12888344113, 48688], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [49712, 50736, 51760, 52784, 53808, 54832], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73839775793, 5573498953, 30722396409, 26293350649, 17619537145, 1100102356327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052025703, 1100001695079, 8895377785, 1100186172795, 1100169462139, 1100119131515], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068800891, 1099867478399, 1099817147775, 13324489113, 8962482585, 8811490713], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099968133575, 56776, 56780, 1099917733331, 1099917734355, 1099917800915], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56784, 55764, 56788, 55768, 56792, 54748], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55772, 56796, 54752, 55776, 56800, 54756], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55780, 56804, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53740, 54764, 55788, 56812, 53744, 54768], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55792, 56816, 1099766735351, 1099766736375, 1099766737399, 52724], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53748, 54772, 55796, 56820, 52728, 53752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54776, 55800, 56824, 52732, 53756, 54780], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55804, 56828, 51712, 52736, 53760, 54784], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55808, 56832, 8761152005, 4399078917, 51716, 52740], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 51720, 52744], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 50700, 51724], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [52748, 53772, 54796, 55820, 56844, 50704], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [51728, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [56852, 49688, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [54808, 55832, 56856, 1099548704287, 49692, 50716], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [70557217, 49696, 50720, 51744, 52768, 53792], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [54816, 55840, 56864, 49700, 50724, 51748], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [52772, 53796, 54820, 55844, 56868, 48680], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [49704, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [55848, 56872, 48684, 49708, 50732, 51756], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [52780, 53804, 54828, 55852, 56876, 4298412593], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [3447345, 48688, 49712, 50736, 51760, 52784], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [53808, 54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69544877109, 26427497725, 21998385405, 13374968061, 1099984916855, 1099934586231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099884255607, 1099850702199, 1100236503423, 1100169395583, 1100169462143, 1100102354303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052023679, 1100001693055, 9012813213, 8861821341, 1100135839135, 56776], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56780, 55760, 56784, 55764, 56788, 55768], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56792, 54748, 55772, 56796, 1099850623459, 1099850624483], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099850691043, 54752, 55776, 56800, 54756, 55780], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56804, 53736, 54760, 55784, 56808, 53740], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54764, 55788, 56812, 53744, 54768, 55792], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56816, 52724, 53748, 54772, 55796, 56820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [52728, 53752, 54776, 55800, 56824, 52732], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53756, 54780, 55804, 56828, 51712, 52736], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 4399078917, 104113669], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [51716, 52740, 53764, 54788, 55812, 56836], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [50700, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56844, 50704, 51728, 52752, 53776, 54800], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55824, 56848, 50708, 51732, 52756, 53780], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [54804, 55828, 56852, 50712, 51736, 52760], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 1099548704287, 49692], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [50716, 51740, 52764, 53788, 54812, 55836], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [56860, 70557217, 53781025, 37070369, 49696, 50720], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49700, 50724, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55844, 56868, 48680, 49704, 50728, 51752], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 42540], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [1099531926063, 48684, 49708, 50732, 51756, 52780], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [53804, 54828, 55852, 56876, 3514929, 42544], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [48688, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [54832, 55856, 56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 140 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56743864377, 21998315797, 21830615317, 4751481109, 8828338541, 1100068801903], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018471279, 1099968140655, 1099833923975, 1099783593351, 8895375765, 1100169393559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100135840151, 1100135906711, 1099984912811, 1099934582187, 1099867474347, 56776], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56780, 56784, 55764, 56788, 55768, 56792], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54748, 55772, 56796, 204777953, 137670113, 137736673], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54752, 55776, 56800, 54756, 55780, 56804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [53736, 54760, 55784, 56808, 53740, 54764], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55788, 56812, 53744, 54768, 55792, 56816], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [52724, 53748, 54772, 55796, 56820, 52728], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53752, 54776, 55800, 56824, 52732, 53756], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54780, 55804, 56828, 51712, 52736, 53760], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [54784, 55808, 56832, 37072389, 45572, 51716], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 45576], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51720, 52744, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [45580, 51724, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56844, 44560, 45584, 50704, 51728, 52752], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 37071381, 44564], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [45588, 50708, 51732, 52756, 53780, 54804], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55828, 56852, 44568, 45592, 50712, 51736], by decide +kernel⟩
private def p19 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 44572], by decide +kernel⟩
private def p20 : P :=
  ⟨unpack [45596, 49692, 50716, 51740, 52764, 53788], by decide +kernel⟩
private def p21 : P :=
  ⟨unpack [54812, 55836, 56860, 43552, 44576, 45600], by decide +kernel⟩
private def p22 : P :=
  ⟨unpack [49696, 50720, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p23 : P :=
  ⟨unpack [55840, 56864, 43556, 44580, 45604, 49700], by decide +kernel⟩
private def p24 : P :=
  ⟨unpack [50724, 51748, 52772, 53796, 54820, 55844], by decide +kernel⟩
private def p25 : P :=
  ⟨unpack [56868, 43560, 44584, 45608, 49704, 50728], by decide +kernel⟩
private def p26 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def p27 : P :=
  ⟨unpack [43564, 44588, 45612, 1099531926063, 48684, 49708], by decide +kernel⟩
private def p28 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def p29 : P :=
  ⟨unpack [56876, 43568, 44592, 45616, 48688, 49712], by decide +kernel⟩
private def p30 : P :=
  ⟨unpack [50736, 51760, 52784, 53808, 54832, 55856], by decide +kernel⟩
private def p31 : P :=
  ⟨unpack [56880], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group2
