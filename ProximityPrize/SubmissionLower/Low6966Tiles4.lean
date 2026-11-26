import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass4
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 1040257033, 4613805065, 18791472141, 61171838993, 87009750053], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [31578243137, 19127276635, 31292133637, 35553816845, 35453424909, 30923782449], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39195023665, 13106594221, 8778076589, 1100035382703, 17552480693, 13207252405], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13089815989, 1099834053087, 1099834054111, 1099834055135, 1099800497639, 1099783650795], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783651819, 1099783652843, 1099783653867, 25924303361, 13056185857, 4449545733], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [154580485, 1099666209287, 8677402129, 34447054357, 21478341161, 12888412713], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4298548777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10117191691, 27482661901, 78251507737, 86942846001, 35604283645, 35369608445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43624139005, 34816242989, 4952873261, 35100957049, 13190477213, 13089818013], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102423967, 17703405985, 13341400481, 17451888033, 39178026409, 1099901163983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901165007, 1099884316115, 1099884317139, 1099884318163, 1099884384723, 4516654565], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4432770537, 1099783650795, 1099783651819, 30303086065, 17418257905, 1099632653839], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099632654863, 8694177297, 4382435857, 1099565543967, 8627067425, 38658063913], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3582505, 3583529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27482661901, 52867579929, 86875599913, 22904424517, 30940493077, 34983941397], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833021205, 35235316057, 26645521753, 13190478217, 1100102420895, 1100102421919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102422943, 1100052092319, 1100068936095, 1100035382687, 39194731945, 13324621229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8962549165, 13106590125, 1099867537879, 1099867538903, 4432769509, 1099800426983], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099800428007, 17451811305, 4415989257, 1099649429003, 1099649430027, 1099649431051], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8660555289, 4365656601, 56860, 1099548841507, 56864, 55844], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56868, 3582505, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36006014993, 69812900893, 74041235509, 31124903205, 26662303013, 34900054309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26226308397, 13375033645, 39245066653, 8878732701, 8778072477, 1100085644703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001759655, 1099968206247, 1099985050023, 1099951496615, 13358174633, 8979325353], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8895507881, 1099901092303, 1099901093327, 1099901094351, 1099800426983, 1099800428007], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733315063, 1099733316087, 1099733317111, 21662823933, 13056183805, 4432765449], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [137800201, 56848, 1099548841495, 56852, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4348878365, 1099548840479, 55836, 56860, 54816, 55840], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56864, 30084979237, 54820, 55844, 56868, 8593444393], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4298545705, 1099515285035, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48606034965, 82530233381, 35604773953, 31041154309, 30772792581, 39111208197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39429619037, 26611967325, 8811631981, 13257518453, 13156924789, 8828407157], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934718375, 1099901164967, 13358173617, 8962547121, 8828332465, 1099951426995], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099917873587, 1099917940147, 1099984977339, 1099984978363, 1099984979387, 1099968203195], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884312019, 1099884313043, 4415990253, 1099766870511, 17418256881, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56840, 4415987213, 121021965, 1099632650767, 1099632651791, 55820], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56844, 55824, 56848, 1099532063255, 54804, 55828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56852, 38725172761, 54808, 55832, 56856, 1099548839455], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 53792, 54816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55840, 56864, 8610289189, 53796, 54820, 55844], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56868, 25773237801, 1099515284011, 52776, 53800, 54824], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
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
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52867713049, 82496814125, 18508794949, 30907006213, 34900057349, 30487724293], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35201763673, 26561703257, 13140148589, 1100068868487, 1100018537863, 1099984984455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985051015, 17518927241, 13156921737, 1100035309999, 1100018533807, 1099984980399], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934649775, 1099901088207, 1099901089231, 1099901090255, 1099901091279, 13257509329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8861882833, 4516652509, 1099833978335, 1099548842491, 56824, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548841475, 56832, 55812, 56836, 55816, 56840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532063247, 54796, 55820, 56844, 54800, 55824], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56848, 4382431765, 87466517, 87467541, 1099599096343, 1099548839447], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 21545381401, 12955518489], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 53788, 54812], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55836, 56860, 1099532061219, 52768, 53792, 54816], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55840, 56864, 34379942437, 52772, 53796, 54820], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [55844, 56868, 1099515282987, 51752, 52776, 53800], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52901467165, 86707963953, 1429658701, 35050981621, 30638714101, 17770663157], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30890087781, 22249960805, 13173632385, 8845180289, 1100135975299, 1100085644679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035314055, 1100001760647, 1099951430023, 13374885277, 13223959965, 1099834056103], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951422915, 1099951423939, 1099917870531, 4499877321, 1099917866443, 1099917867467], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4499807729, 4432766449, 1099548842483, 56820, 56824, 1099699760639], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099699761663, 1099532064255, 55804, 56828, 55808, 56832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099548840455, 54788, 55812, 56836, 54792, 55816], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56840, 54796, 55820, 56844, 1099532062227, 53776], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54800, 55824, 56848, 8677330453, 4382431765, 87467541], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099599096343, 53780, 54804, 55828, 56852, 1099548838427], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 52764], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53788, 54812, 55836, 56860, 21511894561, 52768], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53792, 54816, 55840, 56864, 20357669, 1099532060199], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61306986529, 69628828725, 26377231633, 30437390609, 4835432721, 26762895677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26477821245, 22015154493, 13156923757, 8811628909, 1100068869487, 1099901163927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867610519, 8794845605, 1099968203175, 1099917872551, 1099884319143, 1100018531763], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100018532787, 1099968202163, 8928991681, 4583695809, 4516654529, 1099850757595], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099850758619, 17451810281, 8861880809, 56812, 56816, 1099548841463], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55796, 56820, 1099716537851, 1099716538875, 55800, 56824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55804, 56828, 1099532063235, 54784, 55808, 56832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54788, 55812, 56836, 137799177, 1099649427979, 1099548839435], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53768, 54792, 55816, 56840, 53772, 54796], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55820, 56844, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4382432789, 1099548838423, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56852, 52760, 53784, 54808, 55832, 56856], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 1099548837411], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [73957076005, 44010091581, 26880404745, 26561710345, 30588380425, 17485448509], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100219865407, 1100169534783, 13207184777, 8861955465, 1100169527691, 1100119197067], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068866443, 1100035313035, 1099984982411, 1099934651787, 13291063753, 8895437257], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901089231, 1099901090255, 1099901091279, 4516652505, 1099850755547, 1099850756571], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548843487, 1099532065259, 56808, 56812, 1099548841459, 55792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 55796, 56820, 55800, 56824, 1099532063231], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54780, 55804, 56828, 54784, 55808, 56832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 1099532062219, 53768], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54792, 55816, 56840, 53772, 54796, 55820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56844, 104244753, 1099615873555, 1099548838419, 52752, 53776], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [54800, 55824, 56848, 21562158613, 12972295701, 4382431765], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [87466517, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 1099548837407], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099515281963, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65451096105, 39731902529, 26662369569, 26377229601, 21931340065, 13173705029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169533767, 1100135980359, 1100052089231, 1100001758607, 1099951427983, 1099917874575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8861954449, 1100152749459, 1100135973267, 1100085642643, 9046431157, 8878662069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4566986165, 1099867534807, 1099867535831, 1099532066271, 1099548842471, 56804], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56808, 56812, 1099532064243, 55792, 56816, 55796], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56820, 21679667705, 8794771961, 1099716537851, 1099716538875, 1099548840443], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54776, 55800, 56824, 4432765437, 1099699759615, 54780], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55804, 56828, 54784, 55808, 56832, 1099548839431], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [53764, 54788, 55812, 56836, 53768, 54792], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55816, 56840, 53772, 54796, 55820, 56844], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099548838419, 52752, 53776, 54800, 55824, 56848], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 52760], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [53784, 54808, 55832, 56856, 1099548837407, 51740], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 37134881], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [37135905, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [56864, 4315323941, 51748, 52772, 53796, 54820], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [55844, 56868, 1099515281963, 50728, 51752, 52776], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82396152877, 9868530761, 30923785453, 30655423725, 26226312429, 13106595165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13257516413, 8912287101, 1100219859327, 1099968206207, 1099917875583, 1099934719359], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100068865431, 1100018534807, 1099968204183, 1099917873559, 17552410045, 8962546109], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901089231, 1099901090255, 1099901091279, 4533429721, 1099850755547, 1099850756571], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099548842467, 56804, 56808, 1099548841455, 55788, 56812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55792, 56816, 55796, 56820, 1099548840443, 54776], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55800, 56824, 54780, 55804, 56828, 54784], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55808, 56832, 1099532062215, 53764, 54788, 55812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56836, 53768, 54792, 55816, 56840, 52748], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [53772, 54796, 55820, 56844, 1099548838419, 52752], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [53776, 54800, 55824, 56848, 87467541, 1099599096343], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [52756, 53780, 54804, 55828, 56852, 12955518489], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8643778073, 4332102169, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56856, 1099548837407, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55836, 56860, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55840, 56864, 20357669, 51748, 52772, 53796], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54820, 55844, 56868, 8593511977, 1099515281963, 50728], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [51752, 52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82362667057, 35034206441, 30588384489, 9231062249, 13207254377, 8828405097], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102422891, 1099934651783, 1099884321159, 1099884387719, 13458837901, 13240738189], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895508877, 1100001756583, 1099951425959, 1099901095335, 1099984977339, 1099968201147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850756571, 1099850757595, 1099850758619, 1099548842467, 56800, 4550205925], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4432767461, 56804, 56808, 1099548841455, 55788, 56812], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55792, 56816, 55796, 56820, 1099532063227, 54776], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55800, 56824, 54780, 55804, 56828, 53760], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54784, 55808, 56832, 1099532062215, 53764, 54788], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55812, 56836, 1099649427979, 1099649429003, 53768, 54792], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [55816, 56840, 52748, 53772, 54796, 55820], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [56844, 1099548838419, 52752, 53776, 54800, 55824], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [56848, 52756, 53780, 54804, 55828, 56852], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8660554265, 4365655577, 52760, 53784, 54808, 55832], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [56856, 1099548837407, 51740, 52764, 53788, 54812], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [55836, 56860, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55840, 56864, 20358693, 51748, 52772, 53796], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [54820, 55844, 56868, 1099515281963, 50728, 51752], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69561719861, 30655421697, 30437391617, 1100387638531, 13173701981, 8811629917], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052093279, 13291068817, 8895442321, 8794847633, 1099968204183, 1099917873559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867542935, 1100001756583, 1099951425959, 1099934644679, 1099934645703, 1099934646727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099548843479, 1099833978335, 1099833979359, 1099833980383, 1099548842467, 56800], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56804, 56808, 1099548841455, 55788, 56812, 55792], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56816, 4516584949, 4432766453, 55796, 56820, 1099532063227], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54776, 55800, 56824, 54780, 55804, 56828], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53760, 54784, 55808, 56832, 1099548839431, 53764], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54788, 55812, 56836, 53768, 54792, 55816], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56840, 53772, 54796, 55820, 56844, 1099548838419], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 52756], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [53780, 54804, 55828, 56852, 70690329, 1099582319131], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [52760, 53784, 54808, 55832, 56856, 1099548837407], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [51744, 52768, 53792, 54816, 55840, 56864], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [51748, 52772, 53796, 54820, 55844, 56868], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50728, 51752, 52776, 53800, 54824, 55848], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 138 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56777549881, 22032001309, 17636442397, 9012958493, 1099934651783, 1099884321159], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099884387719, 1100169527695, 1100102419855, 1100052089231, 1100001758607, 1099951427983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8861886885, 1100068861351, 1100068862375, 1100068863399, 1099548842467, 56800], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56804, 4432767465, 137802217, 56808, 1099548841455, 55788], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56812, 55792, 56816, 55796, 56820, 1099548840443], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54776, 55800, 56824, 54780, 55804, 56828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54784, 55808, 56832, 1099548839431, 53764, 54788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55812, 56836, 53768, 54792, 55816, 56840], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [104245773, 37137933, 45580, 53772, 54796, 55820], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [56844, 45584, 1099548838419, 52752, 53776, 54800], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [55824, 56848, 45588, 52756, 53780, 54804], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [55828, 56852, 44568, 45592, 52760, 53784], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [54808, 55832, 56856, 44572, 45596, 1099548837407], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [51740, 52764, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [44576, 45600, 51744, 52768, 53792, 54816], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [55840, 56864, 44580, 45604, 51748, 52772], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [53796, 54820, 55844, 56868, 43560, 44584], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [45608, 50728, 51752, 52776, 53800, 54824], by decide +kernel⟩
private def p18 : P :=
  ⟨unpack [55848, 56872], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18]
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤138) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group4
