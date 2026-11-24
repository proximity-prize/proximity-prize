import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Final50PriceMass
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open P3_6_8_1 (sumBelow sumBelow_eq sumBelow_add)

theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs

theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
    (h : check f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) = P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 12 + (length - 12) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 12 + (length - 12)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 12) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]

private theorem mass_of_checks (f : ℕ → ℕ) (N : ℕ) (values : List ℕ)
    (h : check f 0 N values = true) (hv : values.sum < layerNeed) :
    P3_6_8_1.sumBelow f N < layerNeed := by
  have hs := check_sum f 0 N values h
  have hsum : P3_6_8_1.sumBelow f N = values.sum := by
    simpa only [Nat.zero_add, P3_6_8_1.sumBelow] using hs
  rwa [hsum]

private theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 188 [4718451517351, 3925994697294, 3166456715466, 2510124501966, 1949998257114, 1478942132334, 1089684230154, 774816604206, 526795259226, 337940151054, 200435186634, 106328224014, 47531072346, 15819491886, 2833193994, 79266184] (by decide +kernel) (by decide +kernel)

private theorem m0_1 : availableMass (start .empty) ⟨4,12,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 13 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 150 [4881692334132, 4360203959615, 3299120995004, 2421560994236, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822] (by decide +kernel) (by decide +kernel)

private theorem m0_2 : availableMass (start .empty) ⟨5,8,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,8,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 207 [4518048068509, 3740592468970, 3058235572154, 2466125266570, 1957371117658, 1525195937066, 1162935782650, 864039958474, 622071014810, 430704748138, 283730201146, 175049662730, 98678667994, 48745998250, 19493681018, 5276990026, 564445210, 1029607] (by decide +kernel) (by decide +kernel)

private theorem m0_3 : availableMass (start .empty) ⟨5,15,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 22 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 132 [4881692334132, 4853782898278, 3889042936643, 2689708848203, 1762968763163, 1075751353523, 593935531283, 282350448443, 104775497003, 23940308963, 1524756323] (by decide +kernel) (by decide +kernel)

private theorem m0_4 : availableMass (start .empty) ⟨7,21,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨7,21,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 101 [4881692334132, 4868776427341, 3680746439984, 2143276403084, 1103365678112, 468058125932, 140364849392, 19264193324, 164013012] (by decide +kernel) (by decide +kernel)

private theorem m0_5 : availableMass (start .empty) ⟨8,23,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .empty) ⟨8,23,0⟩ 24 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 3741298433403, 2063764405211, 978279460427, 360480794379, 80875605851, 4841097083] (by decide +kernel) (by decide +kernel)

private theorem m0_6 : availableMass (start .empty) ⟨9,26,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨9,26,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 88 [4881692334132, 4881692334132, 3795231749303, 1928719884780, 799419457700, 228812352092, 27724910868, 114362719] (by decide +kernel) (by decide +kernel)

private theorem m0_7 : availableMass (start .empty) ⟨10,30,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,30,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 94 [4881692334132, 4881692334132, 4881692334132, 4024311291825, 1895284999241, 665813815181, 133509652721, 5477515555] (by decide +kernel) (by decide +kernel)

private theorem m0_8 : availableMass (start .empty) ⟨12,7,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨12,7,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 236 [4507525246264, 3716051133149, 3031069458397, 2444465706421, 1946474034533, 1527828842221, 1179764771149, 894016705157, 662819770261, 478909334653, 335521008701, 226390644949, 145754338117, 88348425101, 49409484973, 24674338981, 10380050549, 3263925277, 563510941, 16899595] (by decide +kernel) (by decide +kernel)

private theorem m0_9 : availableMass (start .empty) ⟨12,36,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨12,36,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4064260637700, 1659644717292, 420655764204, 35897051628, 3600978] (by decide +kernel) (by decide +kernel)

private theorem m0_10 : availableMass (start .empty) ⟨13,39,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨13,39,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4356002924797, 1820062327049, 424280859137, 28102404257] (by decide +kernel) (by decide +kernel)

private theorem m0_11 : availableMass (start .empty) ⟨15,45,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨15,45,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4447493889753, 1710136219038, 286770273018, 5922769167] (by decide +kernel) (by decide +kernel)

private theorem m0_12 : availableMass (start .empty) ⟨18,7,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,7,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 237 [4532535758396, 3658931436343, 2909955197767, 2282299467479, 1762098048295, 1336326382711, 992801552903, 720182280727, 507968927719, 346503495095, 226969623751, 141392594263, 82639326887, 44418381559, 21279957895, 8615895191, 2659672423, 486408247, 18245287, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_13 : availableMass (start .empty) ⟨18,10,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,10,0⟩ 8 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 173 [4801487344399, 3865941302763, 2879355175479, 2093457459235, 1479278291631, 1010073474267, 661324472743, 410738416659, 238248099615, 126011979211, 58414177047, 22064478723, 5798333839, 676855995, 4084712] (by decide +kernel) (by decide +kernel)

private theorem m0_14 : availableMass (start .empty) ⟨18,52,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,52,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 76 [4881692334132, 4881692334132, 4881692334132, 4676679643373, 1839846484196, 230366901380, 1109545896] (by decide +kernel) (by decide +kernel)

private theorem m0_15 : availableMass (start .empty) ⟨19,6,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨19,6,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 277 [4560588876732, 3746824837974, 3038319856638, 2434539834918, 1924698776526, 1498592952054, 1146600898974, 859683421638, 629383591278, 447826746006, 307720490814, 202354697574, 125601505038, 71915318838, 36332811486, 14479437725, 3001467082, 56344278, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_16 : availableMass (start .empty) ⟨20,9,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .empty) ⟨20,9,0⟩ 15 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 198 [4881692334132, 4529991106113, 3490925249313, 2619931904865, 1923017165073, 1375291220337, 953784062145, 637445483073, 407145076785, 245672238033, 137736162657, 69965847585, 30910090833, 11037491505, 2736449793, 315166977, 3126924] (by decide +kernel) (by decide +kernel)

private theorem m0_17 : availableMass (start .empty) ⟨23,51,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨23,51,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 76 [4881692334132, 4881692334132, 4881692334132, 4546052421555, 1631490513377, 192145429409, 688638587] (by decide +kernel) (by decide +kernel)

private theorem m0_18 : availableMass (start .empty) ⟨24,24,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨24,24,0⟩ 33 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 101 [4881692334132, 4881692334132, 4776037778179, 3063469840024, 1488672700888, 595638856984, 168728506456, 22113911704, 193197188] (by decide +kernel) (by decide +kernel)

private theorem m0_19 : availableMass (start .empty) ⟨25,27,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨25,27,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 96 [4881692334132, 4881692334132, 4862626544277, 3268285858083, 1471075720779, 516019824291, 111402881643, 6732421347] (by decide +kernel) (by decide +kernel)

private theorem m0_20 : availableMass (start .empty) ⟨27,6,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨27,6,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 280 [4693626257227, 3802992968038, 2976621506302, 2285749287958, 1715259893422, 1250905824454, 879308504158, 587958276982, 365214408718, 200305288442, 83955006400, 16244056631, 286669557, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_21 : availableMass (start .empty) ⟨30,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨30,3,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 551 [4532979091969, 3772610418610, 3084934838014, 2467634523490, 1916368289758, 1426923162226, 995214376990, 617359522340, 296403490591, 74730755545, 4042915200, 382240, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_22 : availableMass (start .empty) ⟨34,3,0⟩ 4 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,3,0⟩ 4 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 554 [4676597721384, 3875723737484, 3112636257752, 2429161300724, 1820356985120, 1281427556252, 807729040464, 399201702428, 103516258572, 5107597312, 73816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_23 : availableMass (start .empty) ⟨34,17,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,17,0⟩ 29 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 126 [4881692334132, 4881692334132, 4482631694301, 2819036342579, 1585457879715, 808355850899, 358656234563, 128645003763, 31968126179, 3631564115, 30673878] (by decide +kernel) (by decide +kernel)

private theorem m0_24 : availableMass (start .empty) ⟨35,6,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,6,0⟩ 16 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 291 [4881692334132, 4604898833520, 3581257747130, 2679343828514, 1939263382538, 1341811431026, 868938571610, 503750977730, 231000535071, 53345965065, 1369590475, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_25 : availableMass (start .empty) ⟨35,19,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,19,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 117 [4881692334132, 4881692334132, 4646199492222, 2940471301313, 1569083954673, 742161468353, 293334040817, 86147206977, 14061838193, 455645621] (by decide +kernel) (by decide +kernel)

private theorem m0_26 : availableMass (start .empty) ⟨36,9,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨36,9,0⟩ 22 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 205 [4881692334132, 4854458244433, 3916246499070, 2761828023066, 1875389816814, 1212977169402, 734490088638, 403683301050, 188166251886, 59766306171, 4716777185, 4845, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_27 : availableMass (start .empty) ⟨36,21,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨36,21,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 112 [4881692334132, 4881692334132, 4830912485561, 3281648115853, 1683424469701, 750718505413, 269376445837, 65764130077, 6767013493, 25547847] (by decide +kernel) (by decide +kernel)

private theorem m0_28 : availableMass (start .empty) ⟨37,12,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,12,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 160 [4881692334132, 4871134326244, 3867124528178, 2534830011314, 1578576792626, 920341359026, 491129813042, 230977872818, 88950872114, 23144158344, 1621590061, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_29 : availableMass (start .empty) ⟨37,15,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,15,0⟩ 27 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 137 [4881692334132, 4881692334132, 4285629919195, 2689714609470, 1563341103090, 834765711750, 396886865850, 159469139790, 49143251970, 9406064790, 620584650, 560118] (by decide +kernel) (by decide +kernel)

private theorem m0_30 : availableMass (start .empty) ⟨37,23,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,23,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 106 [4881692334132, 4881692334132, 4863828612565, 3355874189360, 1629835377644, 668088747432, 207227136548, 37245805856, 1543046192] (by decide +kernel) (by decide +kernel)

private theorem m0_31 : availableMass (start .empty) ⟨37,26,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,26,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 99 [4881692334132, 4881692334132, 4881692334132, 3427679880044, 1537562043908, 552249258012, 132549079988, 12403225292, 18279599] (by decide +kernel) (by decide +kernel)

private theorem m0_32 : availableMass (start .empty) ⟨38,28,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨38,28,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 4881692334132, 3564955927647, 1520606899580, 500115893276, 99786905532, 5418627164] (by decide +kernel) (by decide +kernel)

private theorem m0_33 : availableMass (start .empty) ⟨40,31,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨40,31,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 93 [4881692334132, 4881692334132, 4881692334132, 4071649821465, 1730694455309, 525163035029, 87449805069, 2587325012] (by decide +kernel) (by decide +kernel)

private theorem m0_34 : availableMass (start .empty) ⟨41,30,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨41,30,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 4881692334132, 4087385071452, 1777565737992, 565134621528, 105438630504, 4708235268] (by decide +kernel) (by decide +kernel)

private theorem m0_35 : availableMass (start .empty) ⟨42,33,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,33,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 91 [4881692334132, 4881692334132, 4881692334132, 4207777601261, 1761272551021, 493029213853, 68015199181, 963501964] (by decide +kernel) (by decide +kernel)

private theorem m0_36 : availableMass (start .empty) ⟨42,48,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,48,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 78 [4881692334132, 4881692334132, 4881692334132, 4544993428800, 1653961625560, 224609107096, 2522322644] (by decide +kernel) (by decide +kernel)

private theorem m0_37 : availableMass (start .empty) ⟨42,51,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,51,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 77 [4881692334132, 4881692334132, 4881692334132, 4665769827009, 1767215916874, 217554854662, 1442243206] (by decide +kernel) (by decide +kernel)

private theorem m0_38 : availableMass (start .empty) ⟨49,50,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨49,50,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 78 [4881692334132, 4881692334132, 4881692334132, 4665041684314, 1769099837940, 225910359068, 2062550457] (by decide +kernel) (by decide +kernel)

private theorem m0_39 : availableMass (start .empty) ⟨51,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .empty) ⟨51,3,0⟩ 15 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 565 [4881692334132, 4531148244419, 3445985860297, 2449919119273, 1567403884969, 791967300393, 188682502205, 3710700747, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_40 : availableMass (start .empty) ⟨56,47,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨56,47,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4537146922332, 1620841129665, 221192062665, 3162957571] (by decide +kernel) (by decide +kernel)

private theorem m0_41 : availableMass (start .empty) ⟨56,48,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨56,48,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4667778180603, 1803896554752, 253028700288, 4025748972] (by decide +kernel) (by decide +kernel)

private theorem m0_42 : availableMass (start .empty) ⟨57,43,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨57,43,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4558625421961, 1762288889737, 305938405721, 11422939647] (by decide +kernel) (by decide +kernel)

private theorem m0_43 : availableMass (start .empty) ⟨64,42,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,42,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4557336170067, 1760098678377, 311735763789, 13462341453] (by decide +kernel) (by decide +kernel)

private theorem m0_44 : availableMass (start .empty) ⟨67,3,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,3,0⟩ 18 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 568 [4881692334132, 4679208404608, 3433744968290, 2173970967038, 1062909977094, 203396659778, 761780326, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_45 : availableMass (start .empty) ⟨67,17,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,17,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 132 [4881692334132, 4881692334132, 4864151114400, 3374293041603, 1649465732291, 668579552075, 185536809607, 13054649052, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_46 : availableMass (start .empty) ⟨68,6,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,6,0⟩ 20 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 295 [4881692334132, 4766966806551, 3462367143845, 2099375761457, 1024826665789, 239504286812, 2085169772, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_47 : availableMass (start .empty) ⟨68,9,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,9,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 206 [4881692334132, 4869311330675, 3715129757841, 2182207505649, 1081259999169, 335634903325, 13439082118, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_48 : availableMass (start .empty) ⟨68,19,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,19,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 122 [4881692334132, 4881692334132, 4881692334132, 3478220714732, 1623853466192, 620255458164, 161022805784, 11793569440, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_49 : availableMass (start .empty) ⟨69,12,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,12,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 162 [4881692334132, 4881692334132, 3905909297365, 2175221592274, 1030364627026, 333284908990, 21987603958, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_50 : availableMass (start .empty) ⟨69,15,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,15,0⟩ 29 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 139 [4881692334132, 4881692334132, 4408814497295, 2495037329242, 1168298591542, 417194276722, 63094206757, 23212671, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_51 : availableMass (start .empty) ⟨69,41,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,41,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4557980990944, 1768160142526, 321486958450, 15928644374] (by decide +kernel) (by decide +kernel)

private theorem m0_52 : availableMass (start .empty) ⟨70,39,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨70,39,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4419633333676, 1643232133322, 311665793390, 17993691098, 108876] (by decide +kernel) (by decide +kernel)

private theorem m0_53 : availableMass (start .empty) ⟨71,32,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,32,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 92 [4881692334132, 4881692334132, 4881692334132, 4147370236719, 1585864238654, 390224174798, 46475412318, 717285055] (by decide +kernel) (by decide +kernel)

private theorem m0_54 : availableMass (start .empty) ⟨71,35,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,35,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 90 [4881692334132, 4881692334132, 4881692334132, 4450825561962, 1796843531693, 415764449389, 42118673965, 290258536] (by decide +kernel) (by decide +kernel)

private theorem m0_55 : availableMass (start .empty) ⟨71,46,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,46,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4665537698731, 1795957977872, 262628237784, 6140058460] (by decide +kernel) (by decide +kernel)

private theorem m0_56 : availableMass (start .empty) ⟨77,45,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨77,45,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4665298278546, 1797816823125, 268521448965, 7353296376] (by decide +kernel) (by decide +kernel)

private theorem m0_57 : availableMass (start .empty) ⟨79,53,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨79,53,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 77 [4881692334132, 4881692334132, 4881692334132, 4756706644185, 1783170876599, 182051622863, 862598101] (by decide +kernel) (by decide +kernel)

private theorem m0_58 : availableMass (start .empty) ⟨80,52,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨80,52,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 77 [4881692334132, 4881692334132, 4881692334132, 4758180539766, 1807543724308, 194830763732, 1288957672] (by decide +kernel) (by decide +kernel)

private theorem m0_59 : availableMass (start .empty) ⟨82,44,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨82,44,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4665656861467, 1804017021500, 275634020892, 8687998464] (by decide +kernel) (by decide +kernel)

private theorem m0_60 : availableMass (start .empty) ⟨85,23,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨85,23,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 108 [4881692334132, 4881692334132, 4881692334132, 3452022177663, 1322364647568, 353520173476, 33338326523, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_61 : availableMass (start .empty) ⟨85,26,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨85,26,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 102 [4881692334132, 4881692334132, 4881692334132, 3813320008777, 1441286573360, 373033410392, 41420529692, 4973675, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_62 : availableMass (start .empty) ⟨86,28,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨86,28,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 98 [4881692334132, 4881692334132, 4881692334132, 3974774103400, 1484667976572, 364279360988, 38558433602, 18645615, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_63 : availableMass (start .empty) ⟨86,37,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨86,37,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 88 [4881692334132, 4881692334132, 4881692334132, 4563226494986, 1809551263014, 357802823954, 25624211414, 41898045] (by decide +kernel) (by decide +kernel)

private theorem m0_64 : availableMass (start .empty) ⟨87,51,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨87,51,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 78 [4881692334132, 4881692334132, 4881692334132, 4757724812750, 1804805847274, 198063076414, 1666088984] (by decide +kernel) (by decide +kernel)

private theorem m0_65 : availableMass (start .empty) ⟨94,42,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,42,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4665060537684, 1802356865331, 279989823759, 10396835403] (by decide +kernel) (by decide +kernel)

private theorem m0_66 : availableMass (start .empty) ⟨94,50,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,50,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4757258012849, 1801009465713, 200084208781, 2040799452] (by decide +kernel) (by decide +kernel)

private theorem m0_67 : availableMass (start .empty) ⟨100,17,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,17,0⟩ 38 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 135 [4881692334132, 4881692334132, 4881692334132, 3747887668373, 1540523837574, 364456917377, 4520610306, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_68 : availableMass (start .empty) ⟨100,49,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,49,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4757103926295, 1800875638502, 202695803562, 2422351106] (by decide +kernel) (by decide +kernel)

private theorem m0_69 : availableMass (start .empty) ⟨101,15,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,15,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 141 [4881692334132, 4881692334132, 4570732723861, 2399768851394, 798995500261, 63796628408, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_70 : availableMass (start .empty) ⟨101,19,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,19,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 125 [4881692334132, 4881692334132, 4881692334132, 3894869102313, 1577123546705, 377250294809, 7315310794, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_71 : availableMass (start .empty) ⟨101,26,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,26,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 105 [4881692334132, 4881692334132, 4881692334132, 4325917669073, 1746746143560, 413497040736, 24725282283, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_72 : availableMass (start .empty) ⟨101,34,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,34,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 92 [4881692334132, 4881692334132, 4881692334132, 4564488353704, 1814816834104, 356013860224, 21994123122, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_73 : availableMass (start .empty) ⟨101,41,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,41,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4664094194295, 1793857756628, 275832659792, 10124626212, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_74 : availableMass (start .empty) ⟨102,28,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨102,28,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 101 [4881692334132, 4881692334132, 4881692334132, 4460930488615, 1836348894220, 422323087404, 27644130812, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_75 : availableMass (start .empty) ⟨106,48,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨106,48,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4756940719394, 1799819820344, 204039645176, 2718858512] (by decide +kernel) (by decide +kernel)

private theorem m0_76 : availableMass (start .empty) ⟨107,40,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨107,40,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 86 [4881692334132, 4881692334132, 4881692334132, 4663730772993, 1789788326166, 272400101190, 9300696647, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_77 : availableMass (start .empty) ⟨110,39,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨110,39,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4665251402778, 1802807910333, 277991253477, 9189170859, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_78 : availableMass (start .empty) ⟨112,47,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨112,47,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4756768346514, 1797807429289, 203933092017, 2845543443] (by decide +kernel) (by decide +kernel)

private theorem m0_79 : availableMass (start .empty) ⟨117,21,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,21,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 118 [4881692334132, 4881692334132, 4881692334132, 3988419144586, 1451907975781, 226110225070, 23203845, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_80 : availableMass (start .empty) ⟨117,23,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,23,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 112 [4881692334132, 4881692334132, 4881692334132, 4149145959525, 1537229566708, 259793270867, 246274785, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_81 : availableMass (start .empty) ⟨117,46,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,46,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4756913677490, 1799893546098, 204716048482, 2841147456] (by decide +kernel) (by decide +kernel)

private theorem m0_82 : availableMass (start .empty) ⟨118,33,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨118,33,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 94 [4881692334132, 4881692334132, 4881692334132, 4552287411829, 1726111679751, 282413764596, 4707001749, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_83 : availableMass (start .empty) ⟨122,45,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,45,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4757051822681, 1801180351011, 204058015491, 2524614853] (by decide +kernel) (by decide +kernel)

private theorem m0_84 : availableMass (start .empty) ⟨126,36,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨126,36,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 90 [4881692334132, 4881692334132, 4881692334132, 4665247304067, 1792718095896, 253661078899, 2159193782, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_85 : availableMass (start .empty) ⟨127,44,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨127,44,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4757182746416, 1801637863424, 201781165712, 1891973259] (by decide +kernel) (by decide +kernel)

private theorem m0_86 : availableMass (start .empty) ⟨129,55,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨129,55,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 77 [4881692334132, 4881692334132, 4881692334132, 4832600902567, 1795901761816, 130824960180, 249015863] (by decide +kernel) (by decide +kernel)

private theorem m0_87 : availableMass (start .empty) ⟨132,43,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨132,43,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4757306416476, 1801235643794, 197698639222, 1085311869] (by decide +kernel) (by decide +kernel)

private theorem m1_0 : availableMass (start .one3) ⟨2,6,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 190 [4677853166212, 3903441583584, 3146863739844, 2493299062632, 1935743973132, 1467058843632, 1079967997524, 767059709304, 520786204572, 333463660032, 197272203492, 104255913864, 46322821164, 15244906512, 2658102132, 67127756] (by decide +kernel) (by decide +kernel)

private theorem m1_1 : availableMass (start .one3) ⟨3,9,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 12 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4740005313959, 3986307280316, 2986780786364, 2167447388348, 1511576120252, 1002006034364, 621146201276, 350975709884, 173043667388, 68469199292, 17941449404, 1719579836, 1027850] (by decide +kernel) (by decide +kernel)

private theorem m1_2 : availableMass (start .one3) ⟨4,12,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .one3) ⟨4,12,0⟩ 27 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4740005313959, 4439709210263, 3820147803099, 2654606381000, 1736389026500, 1056573890600, 581004893300, 274476194600, 100732194500, 22467533000, 1327090100, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_3 : availableMass (start .one3) ⟨6,18,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one3) ⟨6,18,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 121 [4740005313959, 4439709210263, 4152103344383, 3718266552593, 2346389605559, 1235453952431, 543771305111, 174976883759, 28673150519, 556310504, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_4 : availableMass (start .one3) ⟨10,30,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨10,30,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 97 [4740005313959, 4439709210263, 4152103344383, 3858989950569, 2281873071830, 770416307474, 140600526638, 4105120800, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_5 : availableMass (start .one3) ⟨12,36,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨12,36,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 94 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2948657556917, 957692339882, 141519686534, 1689522376] (by decide +kernel) (by decide +kernel)

private theorem m1_6 : availableMass (start .one3) ⟨18,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one3) ⟨18,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 276 [4473592740342, 3662616567726, 2966416944102, 2373692044446, 1873722310614, 1456370451342, 1112081442246, 831882525822, 607383211446, 430775275374, 294832760742, 192911977566, 118951502742, 67472180046, 33577120134, 12961987433, 2426061663, 29682262, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_7 : availableMass (start .one3) ⟨19,6,0⟩ 14 < layerNeed := by
  rw [mass_eq (start .one3) ⟨19,6,0⟩ 14 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 197 [4740005313959, 4126294189867, 3139192607121, 2336600028969, 1698600982041, 1201012355169, 821570838273, 539932922361, 337674899529, 198292862961, 107202706929, 51740126793, 21160619001, 6639481089, 1271811681, 72510489, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_8 : availableMass (start .one3) ⟨26,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3) ⟨26,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 282 [4665211237020, 3803282677522, 2980000069498, 2291632722082, 1723107512458, 1260220239154, 889635622042, 598887302338, 376377842602, 211378726738, 94267066180, 22090280404, 684703607, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_9 : availableMass (start .one3) ⟨34,3,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .one3) ⟨34,3,0⟩ 10 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 285 [4722197938380, 3878325645038, 2933965588166, 2155658515550, 1523979979190, 1020661106894, 628588602278, 331809377016, 118984391636, 12225877770, 10870685, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_10 : availableMass (start .one3) ⟨35,6,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .one3) ⟨35,6,0⟩ 28 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 211 [4740005313959, 4439709210263, 3900375440847, 2797013337627, 1913176565931, 1251403071699, 771887635347, 438679756011, 219683651547, 86658731753, 16876026246, 129180141, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_11 : availableMass (start .one3) ⟨51,3,0⟩ 14 < layerNeed := by
  rw [mass_eq (start .one3) ⟨51,3,0⟩ 14 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 289 [4740005313959, 4034449819813, 2834532442683, 1859969378007, 1089973980243, 497784622856, 97553859952, 657629821, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_12 : availableMass (start .one3) ⟨67,3,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,3,0⟩ 18 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 293 [4740005313959, 4247764990211, 2903331826565, 1711398020273, 782753983817, 140482942376, 242054126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_13 : availableMass (start .one3) ⟨67,6,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,6,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 225 [4740005313959, 4439709210263, 4152103344383, 3675794943739, 2353458806517, 1284594722877, 551578215685, 102437972353, 155895206, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_14 : availableMass (start .one3) ⟨67,28,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,28,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4740005313959, 4439709210263, 4152103344383, 3749334525653, 1757218722789, 471647319501, 67046873221, 1739454204, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_15 : availableMass (start .one3) ⟨68,43,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨68,43,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 88 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2915924548778, 662556656294, 42523748886, 547364] (by decide +kernel) (by decide +kernel)

private theorem m1_16 : availableMass (start .one3) ⟨69,34,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,34,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 92 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2094319166750, 476263977826, 44464559614, 150492578] (by decide +kernel) (by decide +kernel)

private theorem m1_17 : availableMass (start .one3) ⟨69,44,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,44,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 89 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3068405315498, 743953376179, 49641437987, 2017827] (by decide +kernel) (by decide +kernel)

private theorem m1_18 : availableMass (start .one3) ⟨70,24,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨70,24,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4740005313959, 4439709210263, 4152103344383, 3856878747899, 2188855125147, 717628719963, 154628273091, 13698171219, 71566386] (by decide +kernel) (by decide +kernel)

private theorem m1_19 : availableMass (start .one3) ⟨70,39,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨70,39,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3109552465055, 869435173814, 91646854502, 522955576] (by decide +kernel) (by decide +kernel)

private theorem m1_20 : availableMass (start .one3) ⟨71,30,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨71,30,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 102 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2908413326211, 920432241145, 165734420545, 8761357729, 37990] (by decide +kernel) (by decide +kernel)

private theorem m1_21 : availableMass (start .one3) ⟨84,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one3) ⟨84,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 296 [4740005313959, 4373524020994, 3000377456592, 1570356882240, 476885481280, 9968898985, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_22 : availableMass (start .one3) ⟨87,27,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨87,27,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 107 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2914044080331, 934611230795, 174342915815, 10409364406, 1] (by decide +kernel) (by decide +kernel)

private theorem m1_23 : availableMass (start .one3) ⟨100,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,3,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 300 [4740005313959, 4439709210263, 3372522545924, 1665606609908, 386610485394, 842216556, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_24 : availableMass (start .one3) ⟨100,9,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,9,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 184 [4740005313959, 4439709210263, 4152103344383, 3862378124609, 2488255498452, 1009040004228, 170721219398, 11744045, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_25 : availableMass (start .one3) ⟨100,23,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,23,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2939163561997, 983271113060, 185403247484, 5456493033, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_26 : availableMass (start .one3) ⟨100,33,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,33,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3120122295109, 911620068918, 116227766166, 2362729691, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_27 : availableMass (start .one3) ⟨100,48,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,48,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 87 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3161200998863, 689242420727, 29710446623, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_28 : availableMass (start .one3) ⟨101,29,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,29,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 104 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3011194918091, 903662760480, 133536308320, 3404604305, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_29 : availableMass (start .one3) ⟨101,39,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,39,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 94 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3214871768523, 879620898961, 81009889669, 463646498] (by decide +kernel) (by decide +kernel)

private theorem m1_30 : availableMass (start .one3) ⟨101,49,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,49,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 87 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3298551303472, 797191182180, 37090304068, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_31 : availableMass (start .one3) ⟨110,48,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨110,48,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 88 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3296816109029, 792238025569, 37558778449, 5156] (by decide +kernel) (by decide +kernel)

private theorem m1_32 : availableMass (start .one3) ⟨111,46,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨111,46,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 89 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3304528212855, 828435655251, 46049922843, 5131291] (by decide +kernel) (by decide +kernel)

private theorem m1_33 : availableMass (start .one3) ⟨116,3,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,3,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 304 [4740005313959, 4439709210263, 3774105010733, 1904173266424, 401569599505, 151731711, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_34 : availableMass (start .one3) ⟨116,16,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,16,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2852876795037, 977893804079, 130875040806, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_35 : availableMass (start .one3) ⟨116,20,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,20,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2940926440859, 963127955558, 134850741863, 4421275, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_36 : availableMass (start .one3) ⟨117,32,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,32,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3104675776389, 859964686302, 90836922489, 265774753, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_37 : availableMass (start .one3) ⟨117,38,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,38,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3205033060326, 843295532565, 69507688925, 218507689] (by decide +kernel) (by decide +kernel)

private theorem m1_38 : availableMass (start .one3) ⟨117,45,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,45,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 90 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3304698652538, 830287157840, 47208170960, 12242504] (by decide +kernel) (by decide +kernel)

private theorem m1_39 : availableMass (start .one3) ⟨125,44,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨125,44,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 91 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3303476700430, 825071553819, 46315221547, 14422974] (by decide +kernel) (by decide +kernel)

private theorem m1_40 : availableMass (start .one3) ⟨129,43,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨129,43,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 91 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3304927642833, 831529543843, 47610648503, 11930970] (by decide +kernel) (by decide +kernel)

private theorem m2_0 : availableMass (start .one3wide) ⟨2,6,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨2,6,0⟩ 8 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4689306239465, 3926554508103, 3156763113159, 2494647910239, 1932151781391, 1461202492119, 1073712691383, 761579911599, 516686568639, 330899961831, 196072273959, 104040571263, 46626803439, 15637803639, 2865288471, 88074906] (by decide +kernel) (by decide +kernel)

private theorem m2_1 : availableMass (start .one3wide) ⟨3,9,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨3,9,0⟩ 13 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4730647107060, 4032531685422, 3015842359374, 2185454111598, 1522891414926, 1009535414958, 626623930062, 355251451374, 176369142798, 70784841006, 19163055438, 2024968302, 3201930] (by decide +kernel) (by decide +kernel)

private theorem m2_2 : availableMass (start .one3wide) ⟨4,12,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨4,12,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4730647107060, 4414633305120, 3907545735390, 2761065447817, 1814235290185, 1112226600073, 619176854281, 298733641609, 114054662857, 27807730825, 2170770313, 23307] (by decide +kernel) (by decide +kernel)

private theorem m2_3 : availableMass (start .one3wide) ⟨7,21,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨7,21,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4730647107060, 4414633305120, 4113439985052, 3574984426286, 2033557971688, 927126773992, 319021393384, 61494346216, 2231748930, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_4 : availableMass (start .one3wide) ⟨10,28,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨10,28,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 97 [4730647107060, 4414633305120, 4113439985052, 3666065484875, 1898041258297, 641853961585, 118679329913, 3700486954, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_5 : availableMass (start .one3wide) ⟨10,30,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨10,30,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2568381406558, 915263764810, 190071261070, 8817561535, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_6 : availableMass (start .one3wide) ⟨13,39,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨13,39,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 89 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2518496947401, 639593707558, 53452877494, 3512493] (by decide +kernel) (by decide +kernel)

private theorem m2_7 : availableMass (start .one3wide) ⟨18,3,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨18,3,0⟩ 5 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 280 [4617408397546, 3809199387605, 3078950892809, 2457891891869, 1934666625425, 1498537432805, 1139384752025, 847707119789, 614621171489, 431861641205, 291781361705, 187351264445, 112160379569, 60415835909, 26944680257, 7528947401, 434501918, 15, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_8 : availableMass (start .one3wide) ⟨19,6,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨19,6,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 198 [4730647107060, 4158721449040, 3163077847581, 2345836142589, 1698234623277, 1194993809133, 812874953085, 530680041501, 329251794189, 191473664397, 102269838813, 48605237565, 19485514221, 5957055789, 1106982717, 63148893, 1705] (by decide +kernel) (by decide +kernel)

private theorem m2_9 : availableMass (start .one3wide) ⟨26,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨26,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 282 [4655957405127, 3779875945749, 2946407199177, 2251230592413, 1678756987281, 1214301998757, 844085994969, 555234097197, 335776179873, 174653470489, 63449772773, 7682705310, 22316536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_10 : availableMass (start .one3wide) ⟨34,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨34,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 286 [4724712024799, 3919146424171, 2954152012975, 2159737411219, 1515897210391, 1003817409595, 605875415551, 305676482635, 95000078659, 5974087216, 46376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_11 : availableMass (start .one3wide) ⟨35,6,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨35,6,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 212 [4730647107060, 4414633305120, 3918119053882, 2821984915479, 1921548166287, 1248790832151, 762740780271, 426401528919, 206752247439, 74769660055, 10071249707, 6920520, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_12 : availableMass (start .one3wide) ⟨38,18,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨38,18,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 124 [4730647107060, 4414633305120, 4113439985052, 3786148580751, 2400320400086, 1133024965706, 446821850630, 130972776842, 21404237654, 709195853, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_13 : availableMass (start .one3wide) ⟨50,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨50,3,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 290 [4730647107060, 4088049343404, 2891605841589, 1906330813257, 1126935776253, 526479441349, 112481921351, 1100473227, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_14 : availableMass (start .one3wide) ⟨66,3,0⟩ 19 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,3,0⟩ 19 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 294 [4730647107060, 4279167775858, 2975899606595, 1769950364615, 828997947847, 164601096512, 526426726, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_15 : availableMass (start .one3wide) ⟨66,16,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,16,0⟩ 40 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 126 [4730647107060, 4414633305120, 4113439985052, 3320704056039, 1608168081152, 626425736292, 175108166792, 20548002069, 487635, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_16 : availableMass (start .one3wide) ⟨66,28,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,28,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 100 [4730647107060, 4414633305120, 4113439985052, 3805031448376, 2048083976089, 582743693921, 93932800249, 3640704973, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_17 : availableMass (start .one3wide) ⟨66,41,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,41,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 88 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2535004228663, 517951873788, 30859165660, 3197] (by decide +kernel) (by decide +kernel)

private theorem m2_18 : availableMass (start .one3wide) ⟨67,6,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨67,6,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 220 [4730647107060, 4414633305120, 4113439985052, 3210853660815, 1874284710375, 929046610767, 299608459847, 14195084937, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_19 : availableMass (start .one3wide) ⟨67,42,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨67,42,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 91 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3175463643540, 900854861754, 82535761614, 175069378] (by decide +kernel) (by decide +kernel)

private theorem m2_20 : availableMass (start .one3wide) ⟨68,12,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨68,12,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4730647107060, 4414633305120, 4113439985052, 3156932458750, 1601782576857, 675435035097, 194025641101, 12249670943, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_21 : availableMass (start .one3wide) ⟨68,34,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨68,34,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2641574161408, 694631433599, 85932847279, 1181991619] (by decide +kernel) (by decide +kernel)

private theorem m2_22 : availableMass (start .one3wide) ⟨69,45,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨69,45,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 90 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3281383630940, 953627588016, 75757344432, 45442824] (by decide +kernel) (by decide +kernel)

private theorem m2_23 : availableMass (start .one3wide) ⟨70,24,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨70,24,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 111 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2653238797574, 927065814660, 221325985584, 24832710684, 330332193, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_24 : availableMass (start .one3wide) ⟨71,33,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨71,33,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 97 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2817010175568, 803659982904, 114291666216, 2830712346, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_25 : availableMass (start .one3wide) ⟨72,36,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨72,36,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2934968635386, 813519002379, 97724716563, 1214069798] (by decide +kernel) (by decide +kernel)

private theorem m2_26 : availableMass (start .one3wide) ⟨83,3,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨83,3,0⟩ 23 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 298 [4730647107060, 4403692474592, 3208769285880, 1739659607544, 605290455528, 26588429416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_27 : availableMass (start .one3wide) ⟨83,6,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨83,6,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 227 [4730647107060, 4414633305120, 4113439985052, 3715777209314, 2326202405538, 1095003366486, 280582318788, 2535288707, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_28 : availableMass (start .one3wide) ⟨84,43,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨84,43,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 91 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3279812903103, 953541503671, 81428463067, 178010877] (by decide +kernel) (by decide +kernel)

private theorem m2_29 : availableMass (start .one3wide) ⟨99,3,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨99,3,0⟩ 27 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 302 [4730647107060, 4414633305120, 3585622099158, 1869858732656, 527904686830, 5138224636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_30 : availableMass (start .one3wide) ⟨99,9,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨99,9,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 186 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2725976983560, 1155864714648, 238370870863, 302766955, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_31 : availableMass (start .one3wide) ⟨100,12,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨100,12,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2790410860038, 1126039206841, 238151931158, 747252010, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_32 : availableMass (start .one3wide) ⟨100,37,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨100,37,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3033882869616, 788151137696, 74654123776, 517062085] (by decide +kernel) (by decide +kernel)

private theorem m2_33 : availableMass (start .one3wide) ⟨101,42,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨101,42,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 92 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3272430153803, 920176522461, 74395535229, 203144927] (by decide +kernel) (by decide +kernel)

private theorem m2_34 : availableMass (start .one3wide) ⟨101,50,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨101,50,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 88 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3359416888577, 903257692532, 44953818240, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_35 : availableMass (start .one3wide) ⟨102,39,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨102,39,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 94 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3159509939590, 852565524641, 75910561469, 390090217] (by decide +kernel) (by decide +kernel)

private theorem m2_36 : availableMass (start .one3wide) ⟨104,49,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨104,49,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 88 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3360774151223, 914192534034, 48300090754, 473066] (by decide +kernel) (by decide +kernel)

private theorem m2_37 : availableMass (start .one3wide) ⟨114,48,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨114,48,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 89 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3359161859198, 905207750894, 47706943826, 2818750] (by decide +kernel) (by decide +kernel)

private theorem m2_38 : availableMass (start .one3wide) ⟨115,3,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,3,0⟩ 30 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 305 [4730647107060, 4414633305120, 3832024658222, 2008776216028, 467808136809, 564305316, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_39 : availableMass (start .one3wide) ⟨115,31,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,31,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 2565245501980, 569729804136, 43414822846, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_40 : availableMass (start .one3wide) ⟨115,36,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,36,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 97 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3164549562263, 870354293530, 80522757166, 334068448, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_41 : availableMass (start .one3wide) ⟨116,25,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨116,25,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3110589921445, 1012408812502, 140590699878, 170454136, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_42 : availableMass (start .one3wide) ⟨116,41,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨116,41,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3266293209326, 890508061220, 66340820164, 144864490] (by decide +kernel) (by decide +kernel)

private theorem m2_43 : availableMass (start .one3wide) ⟨118,47,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨118,47,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 90 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3360068066310, 912347623009, 49965270989, 8221767] (by decide +kernel) (by decide +kernel)

private theorem m2_44 : availableMass (start .one3wide) ⟨124,39,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨124,39,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3269060084989, 903042608059, 68737448791, 75380918] (by decide +kernel) (by decide +kernel)

private theorem m2_45 : availableMass (start .one3wide) ⟨126,46,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨126,46,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 90 [4730647107060, 4414633305120, 4113439985052, 3826672545960, 3359253558331, 907152405384, 49124643516, 10998575] (by decide +kernel) (by decide +kernel)

private theorem m3_0 : availableMass (start .one4) ⟨2,6,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 180 [4679106249028, 4102294520106, 3243246828205, 2503583618753, 1885165938421, 1377441064009, 969759504317, 651375000145, 411444524293, 239028281561, 123089708749, 52495474657, 16015480085, 2322857833, 26745172] (by decide +kernel) (by decide +kernel)

private theorem m3_1 : availableMass (start .one4) ⟨3,9,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 33 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4679106249028, 4274622143268, 3861931290683, 2978163270985, 2097359300961, 1408756390689, 889423603465, 516080732313, 265098299985, 112497558961, 33950491449, 4779809385, 47370185, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_2 : availableMass (start .one4) ⟨6,18,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,18,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4679106249028, 4274622143268, 3894297784836, 3477545805961, 2226099645051, 1118082149415, 455770658611, 126569611935, 14203499883, 35031507] (by decide +kernel) (by decide +kernel)

private theorem m3_3 : availableMass (start .one4) ⟨9,27,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one4) ⟨9,27,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 106 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2833139453956, 1211795890326, 330518328562, 35042526558, 53596188] (by decide +kernel) (by decide +kernel)

private theorem m3_4 : availableMass (start .one4) ⟨10,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one4) ⟨10,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 236 [4476038483711, 3686821622599, 3005853231271, 2422885288223, 1928170014127, 1512459871831, 1167007566359, 883566044911, 654388496863, 472228353767, 330339289351, 222475219519, 142890302351, 86338938103, 48075769207, 23855680271, 9933798079, 3065491591, 506371943, 12876184] (by decide +kernel) (by decide +kernel)

private theorem m3_5 : availableMass (start .one4) ⟨12,36,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one4) ⟨12,36,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 96 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2939344119990, 1073238327264, 165169021792, 2393611744] (by decide +kernel) (by decide +kernel)

private theorem m3_6 : availableMass (start .one4) ⟨18,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one4) ⟨18,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 242 [4619283178417, 3770733314694, 2979338980234, 2319306030726, 1775257522938, 1332771952486, 978383253834, 699580800294, 484809404026, 323469316038, 205916226186, 123461263174, 68370994554, 33867426726, 14128004938, 4285631806, 509502326, 119245, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_7 : availableMass (start .one4) ⟨34,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one4) ⟨34,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 246 [4673283426002, 3795084118898, 2794436408654, 1991823488034, 1360538961518, 875742265778, 514458669678, 255580386649, 82344136260, 5855593879, 46376, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_8 : availableMass (start .one4) ⟨35,6,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .one4) ⟨35,6,0⟩ 31 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 196 [4679106249028, 4274622143268, 3794441747347, 2728281309240, 1810550042048, 1142755005896, 675472981584, 364658285912, 171642771680, 63135827688, 11718608629, 64865601, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_9 : availableMass (start .one4) ⟨37,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one4) ⟨37,15,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2574916143673, 1312016396873, 581151758425, 207568031401, 50977658489, 5559721993, 36142265, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_10 : availableMass (start .one4) ⟨50,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one4) ⟨50,3,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 250 [4679106249028, 3959660101401, 2737784546122, 1762487927670, 1018415767578, 469987573680, 104138860596, 1100473227, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_11 : availableMass (start .one4) ⟨66,3,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one4) ⟨66,3,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 255 [4679106249028, 4187731061402, 2909036421087, 1711556977903, 812316339829, 186758290188, 1295964991, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_12 : availableMass (start .one4) ⟨67,6,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,6,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 211 [4679106249028, 4274622143268, 3894297784836, 3510594860749, 2408922610228, 1314875620844, 589029224740, 148436519630, 1897544628, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_13 : availableMass (start .one4) ⟨68,42,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one4) ⟨68,42,0⟩ 58 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3128265962504, 1135181976749, 115574297121, 471000669] (by decide +kernel) (by decide +kernel)

private theorem m3_14 : availableMass (start .one4) ⟨70,27,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one4) ⟨70,27,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3095201910929, 1363550856641, 322037594137, 34484088265, 320440255, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_15 : availableMass (start .one4) ⟨70,38,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨70,38,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3179285086830, 1372116495305, 196207093613, 4289030194, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_16 : availableMass (start .one4) ⟨72,39,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨72,39,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1515067025892, 217932393192, 4911805965, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_17 : availableMass (start .one4) ⟨72,44,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨72,44,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1615909898580, 190518228852, 1755561414] (by decide +kernel) (by decide +kernel)

private theorem m3_18 : availableMass (start .one4) ⟨83,3,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .one4) ⟨83,3,0⟩ 24 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 259 [4679106249028, 4274622143268, 3153178885006, 1703811206562, 627161599998, 40516014597, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_19 : availableMass (start .one4) ⟨99,3,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,3,0⟩ 28 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 263 [4679106249028, 4274622143268, 3496772497504, 1843888621998, 569072579497, 11181685446, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_20 : availableMass (start .one4) ⟨99,9,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,9,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2686079284319, 1177469102994, 295614532008, 3236278434, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_21 : availableMass (start .one4) ⟨99,18,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,18,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 130 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2968992035613, 1255772266122, 311053334842, 20206451819, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_22 : availableMass (start .one4) ⟨99,29,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,29,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 109 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3181405259320, 1475536265659, 279291762451, 17496323926, 487591, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_23 : availableMass (start .one4) ⟨100,22,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one4) ⟨100,22,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3027217134627, 1245530634983, 273355796835, 17581774705, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_24 : availableMass (start .one4) ⟨102,36,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨102,36,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1490061116544, 209552494912, 5860668556, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_25 : availableMass (start .one4) ⟨109,49,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨109,49,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1665621357211, 139414237595, 318770503] (by decide +kernel) (by decide +kernel)

private theorem m3_26 : availableMass (start .one4) ⟨110,39,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨110,39,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1609956464650, 198863442142, 3677355918, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_27 : availableMass (start .one4) ⟨115,3,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,3,0⟩ 32 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 267 [4679106249028, 4274622143268, 3768299735152, 2120247532098, 614694187414, 6093813044, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_28 : availableMass (start .one4) ⟨115,16,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,16,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3105291279397, 1449702547714, 335373163590, 7653231532, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_29 : availableMass (start .one4) ⟨115,20,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,20,0⟩ 58 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 126 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3148085238680, 1475931957904, 320656697488, 11192399564, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_30 : availableMass (start .one4) ⟨117,48,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨117,48,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1663855155617, 140064223576, 406051274] (by decide +kernel) (by decide +kernel)

private theorem m3_31 : availableMass (start .one4) ⟨124,47,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨124,47,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 94 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1663542399631, 141008777132, 489732889] (by decide +kernel) (by decide +kernel)

private theorem m3_32 : availableMass (start .one4) ⟨128,46,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨128,46,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1668512174777, 144682571385, 602152745] (by decide +kernel) (by decide +kernel)

private theorem m4_0 : availableMass (start .one5) ⟨1,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4493299453530, 3743656464938, 3081393605882, 2501366173386, 1998372841370, 1567155660650, 1202400058938, 898734840842, 650732187866, 452907658410, 299720187770, 185572088138, 104809048602, 51720135146, 20537790650, 5437834890, 539464538, 471631] (by decide +kernel) (by decide +kernel)

private theorem m4_1 : availableMass (start .one5) ⟨2,6,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 16 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 166 [4628005587678, 4002844205946, 3094037448366, 2315763360682, 1678969766790, 1170088179714, 775320115678, 480637094106, 271780637622, 134262272050, 53363526414, 14135932938, 1401027046, 1209953] (by decide +kernel) (by decide +kernel)

private theorem m4_2 : availableMass (start .one5) ⟨3,9,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 33 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4628005587678, 4137434455250, 3651469505526, 2732740782930, 1848996279794, 1178102903762, 691893102834, 361554463058, 157629708530, 50016701394, 7968441842, 139034786, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_3 : availableMass (start .one5) ⟨5,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2415273024108, 1324174440828, 622213449868, 225980412828, 49190299308, 2682827323, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_4 : availableMass (start .one5) ⟨8,24,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one5) ⟨8,24,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2862780602178, 1669495265644, 580671791264, 114040024108, 4370303396, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_5 : availableMass (start .one5) ⟨10,3,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one5) ⟨10,3,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 209 [4491263709955, 3627881035692, 2886070032588, 2262159124972, 1743299881740, 1317351660588, 972881608012, 699164659308, 486183538572, 324628758700, 205898621388, 122099217132, 66044425228, 31255913772, 11963139660, 3103348588, 321575052, 635168] (by decide +kernel) (by decide +kernel)

private theorem m4_6 : availableMass (start .one5) ⟨18,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one5) ⟨18,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 227 [4628005587678, 4116004076135, 3314136603468, 2537280104268, 1905772078924, 1400235629388, 1002681123660, 696506195788, 466495745868, 298821940044, 181044210508, 102109255500, 52351039308, 23490792268, 8637010764, 2285457228, 319160140, 8417310, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_7 : availableMass (start .one5) ⟨34,3,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .one5) ⟨34,3,0⟩ 32 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 238 [4628005587678, 4137434455250, 3635996579794, 2740880733016, 1925390216664, 1300226395224, 834089668312, 498426656088, 267430199256, 118039359110, 30797876002, 919821205, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_8 : availableMass (start .one5) ⟨50,3,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one5) ⟨50,3,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 249 [4628005587678, 4137434455250, 3682501885502, 3180667901260, 2219164872340, 1399808687668, 804275693012, 390737929588, 122339922724, 5834229031, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_9 : availableMass (start .one5) ⟨67,6,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨67,6,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 199 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2404367706108, 1305771873432, 599719444492, 185867999852, 10211609868, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_10 : availableMass (start .one5) ⟨68,42,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one5) ⟨68,42,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 95 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1247221390579, 126934282787, 488763188] (by decide +kernel) (by decide +kernel)

private theorem m4_11 : availableMass (start .one5) ⟨69,21,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,21,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 125 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1893001656427, 618651239184, 130432165488, 10902182224, 39713954, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_12 : availableMass (start .one5) ⟨71,41,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one5) ⟨71,41,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2127807949507, 433149977674, 16530980203, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_13 : availableMass (start .one5) ⟨72,36,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one5) ⟨72,36,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 106 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2159499009296, 519832198383, 36166602671, 6341548] (by decide +kernel) (by decide +kernel)

private theorem m4_14 : availableMass (start .one5) ⟨99,6,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,6,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2817625572099, 1614193792696, 603247495500, 69442042723, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_15 : availableMass (start .one5) ⟨99,15,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,15,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 142 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1682902574794, 528127060746, 79285254253, 26061271, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_16 : availableMass (start .one5) ⟨99,39,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,39,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 104 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2224192707136, 492100335412, 23613294852, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_17 : availableMass (start .one5) ⟨101,27,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one5) ⟨101,27,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2091877601170, 550414770422, 61396570022, 721993971, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_18 : availableMass (start .one5) ⟨101,45,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨101,45,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2296662690286, 485730307958, 14133319994, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_19 : availableMass (start .one5) ⟨116,38,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨116,38,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 105 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2217770708857, 473995477534, 21406620402, 209565] (by decide +kernel) (by decide +kernel)

private theorem m4_20 : availableMass (start .one5) ⟨116,42,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨116,42,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 103 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2299691277837, 502069620851, 18025981219, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_21 : availableMass (start .one5) ⟨124,41,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨124,41,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 103 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2299302391723, 501339682041, 18348495405, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_0 : availableMass (start .one6) ⟨1,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 204 [4577344072499, 3992070205709, 3285692264229, 2612641512381, 2036972810301, 1551572984229, 1149192811509, 822447020589, 563814291021, 365637253461, 220122489669, 119340532509, 55225865949, 19576925061, 4056096021, 189858164, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_1 : availableMass (start .one6) ⟨2,6,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one6) ⟨2,6,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 178 [4577344072499, 4003054728023, 3477982715867, 2915983158981, 2136973359014, 1487543577398, 983690607302, 607805603414, 341849738726, 167354204534, 65420210438, 16718984342, 1491772454, 356527, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_2 : availableMass (start .one6) ⟨4,12,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one6) ⟨4,12,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2455938977734, 1507078264491, 794886909399, 351145274787, 113914161423, 19077587739, 406319214, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_3 : availableMass (start .one6) ⟨7,21,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one6) ⟨7,21,0⟩ 63 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 124 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1824114814279, 728338203663, 186854010423, 16646589519, 3625216, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_4 : availableMass (start .one6) ⟨9,27,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .one6) ⟨9,27,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2114857757267, 924839545703, 191477069879, 8726110089, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_5 : availableMass (start .one6) ⟨34,3,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one6) ⟨34,3,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 226 [4577344072499, 4003054728023, 3477982715867, 2942613267961, 2110203153465, 1412896353081, 902042609001, 541476009609, 298885362009, 145814192025, 57660744201, 13736500557, 335392085, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_6 : availableMass (start .one6) ⟨66,3,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one6) ⟨66,3,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 239 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2514945430275, 1615769821887, 870636939567, 380718361527, 87842347059, 480775625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_7 : availableMass (start .one6) ⟨69,18,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one6) ⟨69,18,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 133 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1910259179105, 721082447924, 178942016084, 21867106676, 389796216, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_8 : availableMass (start .one6) ⟨69,34,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .one6) ⟨69,34,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1293964492860, 201932309812, 5013434515, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_9 : availableMass (start .one6) ⟨99,6,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,6,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 196 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2558916187189, 1549747126350, 598233413070, 97731031117, 487635, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_10 : availableMass (start .one6) ⟨99,15,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,15,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1551149508756, 469780860936, 72733118291, 197653345, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_11 : availableMass (start .one6) ⟨99,27,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,27,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2133647433374, 806947405298, 111141276398, 2939313269, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_12 : availableMass (start .one6) ⟨100,21,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .one6) ⟨100,21,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1200358193523, 265621262667, 24006771771, 37422292, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_13 : availableMass (start .one6) ⟨101,27,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .one6) ⟨101,27,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 125 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1324922118405, 249816959424, 14485587084, 5652638, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_14 : availableMass (start .one6) ⟨115,39,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .one6) ⟨115,39,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1415964222029, 180408844038, 1925467702, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_0 : availableMass (start .one7) ⟨1,3,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 185 [4518321774336, 3832102945425, 3048257003135, 2339452199523, 1749338033831, 1267330678859, 882749539407, 584817252275, 362659686263, 205305942171, 101688352799, 40642482947, 10907129415, 1124321003, 1426177, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_1 : availableMass (start .one7) ⟨2,6,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one7) ⟨2,6,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4518321774336, 3849816668780, 3250457160752, 2563065127541, 1772343319107, 1160794709835, 708437438323, 391809945723, 187101402915, 70151710507, 16451498835, 1142127963, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_2 : availableMass (start .one7) ⟨3,9,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one7) ⟨3,9,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2240678456940, 1548498657716, 888277214484, 448205700212, 184474642388, 52368598836, 6266157716, 24476014, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_3 : availableMass (start .one7) ⟨6,18,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one7) ⟨6,18,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1660181020988, 723456919908, 209838754952, 26409124796, 138828190, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_4 : availableMass (start .one7) ⟨7,21,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .one7) ⟨7,21,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1378809679254, 543357655526, 110069429174, 4709555545, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_5 : availableMass (start .one7) ⟨11,33,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .one7) ⟨11,33,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1136133599853, 351541021640, 17243918062, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_6 : availableMass (start .one7) ⟨34,3,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one7) ⟨34,3,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 206 [4518321774336, 3849816668780, 3250457160752, 2618520246235, 1770337089116, 1124199335972, 672133370988, 371043219764, 183210443900, 76294140996, 23330944652, 2941209607, 149065, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_7 : availableMass (start .one7) ⟨34,6,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .one7) ⟨34,6,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 205 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1427104281075, 845975360333, 433138268397, 193589507885, 70431608141, 18080418189, 2265106733, 32491083, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_8 : availableMass (start .one7) ⟨37,18,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .one7) ⟨37,18,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1053595503513, 369465044503, 68975564943, 3007995775, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_9 : availableMass (start .one7) ⟨66,3,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one7) ⟨66,3,0⟩ 63 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 228 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1657950888561, 906807355910, 419948215086, 137930686142, 10992590108, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_10 : availableMass (start .one7) ⟨68,15,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .one7) ⟨68,15,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 888559908195, 263528301756, 45926051956, 2326214124, 60489, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_11 : availableMass (start .one7) ⟨68,32,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .one7) ⟨68,32,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 136 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1132981164636, 320789685960, 14473718208, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_12 : availableMass (start .one7) ⟨98,3,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .one7) ⟨98,3,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 251 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 976401801486, 401814225338, 86984392283, 109080280, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_0 : availableMass (start .two6thin) ⟨1,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨1,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 194 [4575346952499, 3836290418634, 3088561183374, 2443266679386, 1893391990446, 1431786151434, 1051162148334, 744096918234, 503031349326, 320270280906, 187982503374, 98200758234, 42821738094, 13606086666, 2178398766, 38927848, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_1 : availableMass (start .two6thin) ⟨2,6,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨2,6,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 183 [4577344072499, 4003054728023, 3477982715867, 2991093170456, 2292194256284, 1610259420188, 1077515784092, 676444082204, 389095067036, 197089509404, 81618198428, 23441941532, 2891564444, 13660212, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_2 : availableMass (start .two6thin) ⟨4,12,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨4,12,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1920052488174, 1074671733351, 519136533939, 197909127327, 47840990763, 3606819159, 3463, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_3 : availableMass (start .two6thin) ⟨8,24,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨8,24,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1856290197719, 679802196635, 138232209455, 5947852450, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_4 : availableMass (start .two6thin) ⟨10,30,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨10,30,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 117 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1121101879788, 222424009452, 8738823834, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_5 : availableMass (start .two6thin) ⟨18,3,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨18,3,0⟩ 24 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4577344072499, 4003054728023, 3237556875087, 2413857022455, 1758005034807, 1245545703183, 853943619711, 562583177607, 352768571175, 207723795807, 112592647983, 54438725271, 22245426327, 6915950895, 1273299807, 60274983, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_6 : availableMass (start .two6thin) ⟨34,3,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨34,3,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 220 [4577344072499, 4003054728023, 3477982715867, 2746164090201, 1888241268777, 1245931317033, 780188621721, 455822288313, 241496141001, 109728722697, 36893514322, 4559418484, 319311, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_7 : availableMass (start .two6thin) ⟨50,3,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨50,3,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 233 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2330768892160, 1470897076590, 857384237826, 443309515470, 182600202834, 37181743355, 146353766, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_8 : availableMass (start .two6thin) ⟨69,21,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨69,21,0⟩ 71 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 132 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2166355397039, 1075769015937, 271349545713, 33703952001, 553952038, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_9 : availableMass (start .two6thin) ⟨70,39,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨70,39,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1351014452641, 180965175216, 1911521091, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_10 : availableMass (start .two6thin) ⟨99,6,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨99,6,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 204 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2070206882338, 1037588945046, 337399792854, 25009463842, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_11 : availableMass (start .two6thin) ⟨99,15,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨99,15,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2115552395814, 953152734792, 239014948116, 21255289744, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_12 : availableMass (start .two6thin) ⟨101,27,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨101,27,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 125 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1324922118405, 249816959424, 14485587084, 5652638, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_13 : availableMass (start .two6thin) ⟨101,44,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨101,44,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1396197808513, 150509652062, 498481594, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_14 : availableMass (start .two6thin) ⟨116,40,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨116,40,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1409338349103, 171103423031, 1454109489, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_15 : availableMass (start .two6thin) ⟨128,48,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨128,48,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1462358543167, 143191637775, 191888397] (by decide +kernel) (by decide +kernel)

private theorem m8_0 : availableMass (start .two6thinwide) ⟨1,3,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨1,3,0⟩ 16 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 199 [4559471596449, 3892667695891, 3127396892406, 2462271637434, 1899982285998, 1431516438546, 1047967511334, 740534736426, 500523161694, 319343650818, 188512883286, 99653354394, 44493375246, 14867072754, 2714389638, 83171528, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_1 : availableMass (start .two6thinwide) ⟨2,6,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨2,6,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4559471596449, 3958106273613, 3199004072542, 2327752936270, 1631964717118, 1091535780142, 686505817630, 397057849102, 203518221310, 86356608238, 26186011102, 3762758350, 42035009, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_2 : availableMass (start .two6thinwide) ⟨3,9,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨3,9,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 167 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2459422720870, 1705607892732, 1034734480248, 568368850404, 269134492800, 99724881036, 22903472712, 1503709428, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_3 : availableMass (start .two6thinwide) ⟨10,28,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨10,28,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 107 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2470760588469, 1258770528481, 304152817949, 22992448249, 35674] (by decide +kernel) (by decide +kernel)

private theorem m8_4 : availableMass (start .two6thinwide) ⟨10,30,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨10,30,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 121 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1414818609543, 361423264008, 27598888776, 74616, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_5 : availableMass (start .two6thinwide) ⟨17,3,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨17,3,0⟩ 35 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 218 [4559471596449, 3958106273613, 3410661485849, 2687781502992, 1966213158060, 1400528996256, 966513993708, 641993859984, 406835038092, 242944704480, 134270769036, 66801875088, 28567399404, 9637452192, 2122877100, 175251216, 178376, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_6 : availableMass (start .two6thinwide) ⟨34,6,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨34,6,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 186 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2190689657406, 1341187086510, 766477904670, 399757687182, 183538279422, 69647796846, 19230624990, 2747419765, 31499117, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_7 : availableMass (start .two6thinwide) ⟨38,21,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨38,21,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 133 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1172058036018, 349956108438, 56941187370, 1610925827, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_8 : availableMass (start .two6thinwide) ⟨39,39,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨39,39,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1400924276367, 234314854854, 3996716158, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_9 : availableMass (start .two6thinwide) ⟨65,15,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨65,15,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 1652271966569, 623120389831, 170234642575, 25228782487, 716918563, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_10 : availableMass (start .two6thinwide) ⟨66,6,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,6,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 199 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 1794583071842, 911482032668, 380960989628, 101775150210, 3356751321, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_11 : availableMass (start .two6thinwide) ⟨66,9,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,9,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 180 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2070693625433, 1208830214943, 510633093303, 163190854863, 26060993353, 33843919, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_12 : availableMass (start .two6thinwide) ⟨66,17,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,17,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1336702985673, 438794177867, 93485847915, 8060081387, 37100502, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_13 : availableMass (start .two6thinwide) ⟨66,39,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,39,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1539705568563, 303833663532, 7986274094, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_14 : availableMass (start .two6thinwide) ⟨66,40,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,40,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1601459947801, 349251591331, 10008500902, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_15 : availableMass (start .two6thinwide) ⟨67,24,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨67,24,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 130 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1330636169133, 334813620960, 38222693496, 414527022, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_16 : availableMass (start .two6thinwide) ⟨70,30,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨70,30,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 122 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1435385854243, 317542385418, 20780172186, 2256509, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_17 : availableMass (start .two6thinwide) ⟨82,39,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨82,39,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1599016865820, 343153244622, 10331960385, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_18 : availableMass (start .two6thinwide) ⟨84,38,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨84,38,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1459674872909, 246464095284, 5335807378, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_19 : availableMass (start .two6thinwide) ⟨88,48,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨88,48,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 111 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1638849583449, 311847697125, 3069618543, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_20 : availableMass (start .two6thinwide) ⟨90,47,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨90,47,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1640015964273, 318995514878, 3676393629, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_21 : availableMass (start .two6thinwide) ⟨92,46,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨92,46,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1641183406028, 326249135006, 4364317951, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_22 : availableMass (start .two6thinwide) ⟨93,45,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨93,45,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1642544752627, 334520222139, 5185551042, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_23 : availableMass (start .two6thinwide) ⟨97,3,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨97,3,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 221 [4559471596449, 3958106273613, 3413598370713, 2470049011626, 1137000237540, 263052332180, 599325726, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_24 : availableMass (start .two6thinwide) ⟨98,12,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,12,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 165 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1341817737258, 432086611707, 66991666964, 20454855, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_25 : availableMass (start .two6thinwide) ⟨98,28,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,28,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 125 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1425132021001, 300392117061, 19147729153, 15314195, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_26 : availableMass (start .two6thinwide) ⟨98,33,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,33,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1475158680347, 285039057925, 11520258661, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_27 : availableMass (start .two6thinwide) ⟨98,38,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,38,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1529168947550, 280240939098, 6932431813, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_28 : availableMass (start .two6thinwide) ⟨99,31,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨99,31,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1553902994233, 358445366341, 21037884893, 5839296, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_29 : availableMass (start .two6thinwide) ⟨99,36,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨99,36,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1601202325338, 356420887872, 13882623216, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_30 : availableMass (start .two6thinwide) ⟨103,44,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨103,44,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1642162430735, 334399530866, 5614335893, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_31 : availableMass (start .two6thinwide) ⟨112,43,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨112,43,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1641956269139, 334765943241, 6030260592, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_32 : availableMass (start .two6thinwide) ⟨113,3,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨113,3,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 227 [4559471596449, 3958106273613, 3413598370713, 2829458911192, 1482572195418, 390556812412, 2208806620, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_33 : availableMass (start .two6thinwide) ⟨113,27,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨113,27,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 129 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1561823984672, 385569549214, 27640926106, 20274426, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_34 : availableMass (start .two6thinwide) ⟨114,25,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨114,25,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 130 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1430367511778, 309596601210, 19848134429, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_35 : availableMass (start .two6thinwide) ⟨118,33,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨118,33,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 122 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1602569132603, 364048251315, 16162618299, 291625, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_36 : availableMass (start .two6thinwide) ⟨121,42,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨121,42,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1641733238022, 334671455076, 6353181828, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_0 : availableMass (start .two6wide) ⟨1,3,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨1,3,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 225 [4487981692249, 3778312455973, 3156060990097, 2586487017551, 1973379826584, 1459772880444, 1051412828112, 733355706132, 491730825672, 313740772524, 187661407104, 102841864452, 49704554232, 19745160732, 5532642864, 709234164, 5609844, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_1 : availableMass (start .two6wide) ⟨3,9,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨3,9,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1698543458221, 1074092633278, 599458106698, 296248491718, 121168964338, 35473660558, 4965676378, 57136184, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_2 : availableMass (start .two6wide) ⟨6,18,0⟩ 87 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨6,18,0⟩ 87 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 935101356562, 355599281404, 86707639612, 7295580028, 1226818, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_3 : availableMass (start .two6wide) ⟨9,27,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨9,27,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 142 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1049143901094, 360553866820, 45969234784, 308894753, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_4 : availableMass (start .two6wide) ⟨10,28,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨10,28,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 655890971345, 130013487561, 5181501172, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_5 : availableMass (start .two6wide) ⟨11,31,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨11,31,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 719062805123, 143779498496, 4620175751, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_6 : availableMass (start .two6wide) ⟨31,3,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨31,3,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 248 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1671673199433, 1065517378149, 619337624421, 321616083981, 136753295709, 34284565650, 755028792, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_7 : availableMass (start .two6wide) ⟨34,15,0⟩ 98 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨34,15,0⟩ 98 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 176 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 682598650280, 228161864441, 49827240281, 4345008689, 12607483, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_8 : availableMass (start .two6wide) ⟨46,3,0⟩ 89 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨46,3,0⟩ 89 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 272 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1043806127961, 572688860169, 254480409849, 69913105855, 1805125073, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_9 : availableMass (start .two6wide) ⟨61,27,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨61,27,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 666457932403, 113412670356, 4283709456, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_10 : availableMass (start .two6wide) ⟨62,28,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨62,28,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 703375315165, 125026700177, 4667846873, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_11 : availableMass (start .two6wide) ⟨63,31,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,31,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 798418345353, 176331575787, 6938311825, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_12 : availableMass (start .two6wide) ⟨79,43,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨79,43,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 811262212515, 133878113027, 775128396, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_13 : availableMass (start .two6wide) ⟨80,30,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨80,30,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 796107390558, 167595700332, 5978378604, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_14 : availableMass (start .two6wide) ⟨92,9,0⟩ 97 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,9,0⟩ 97 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 610392249800, 129383799197, 805860152, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_15 : availableMass (start .two6wide) ⟨92,12,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,12,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 190 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 672189312391, 150928063285, 3559511756, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_16 : availableMass (start .two6wide) ⟨92,20,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,20,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 713818446513, 141586627371, 5033712236, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_17 : availableMass (start .two6wide) ⟨92,24,0⟩ 102 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,24,0⟩ 102 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 738725109191, 139959364785, 4737038182, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_18 : availableMass (start .two6wide) ⟨92,42,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,42,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 810439415970, 131114786232, 796018884, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_19 : availableMass (start .two6wide) ⟨92,46,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,46,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 834373688236, 148297598524, 649042162, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_20 : availableMass (start .two6wide) ⟨100,41,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨100,41,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 810234277461, 130633485646, 846087634, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_21 : availableMass (start .two6wide) ⟨100,45,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨100,45,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 834266678046, 148030550706, 711709350, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_22 : availableMass (start .two6wide) ⟨104,44,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨104,44,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 834427517074, 149618881165, 814679116, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_23 : availableMass (start .two6wide) ⟨107,28,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨107,28,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 792853506752, 153036390838, 3158239257, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_24 : availableMass (start .two6wide) ⟨107,33,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨107,33,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 815884698984, 159177346146, 2727761995, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_25 : availableMass (start .two6wide) ⟨111,43,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨111,43,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 834381516354, 149510810654, 855067404, 0] (by decide +kernel) (by decide +kernel)

private theorem m9_26 : availableMass (start .two6wide) ⟨117,42,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨117,42,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 834400555171, 149751317806, 881935852, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_0 : availableMass (start .two6wider) ⟨1,3,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨1,3,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 255 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1250066140980, 882485958192, 601706767308, 393093654216, 243326844132, 140401701600, 73628730492, 33633574008, 12357014676, 3054974352, 298514220, 513884, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_1 : availableMass (start .two6wider) ⟨4,12,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨4,12,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 181 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 972910816546, 505128335283, 209451630447, 63645467211, 9983123271, 199978086, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_2 : availableMass (start .two6wider) ⟨12,36,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨12,36,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 580123944680, 151532259611, 3828514158, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_3 : availableMass (start .two6wider) ⟨31,15,0⟩ 93 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨31,15,0⟩ 93 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1000764307470, 465375399736, 137683439428, 24087148600, 1192666900, 371, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_4 : availableMass (start .two6wider) ⟨32,6,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨32,6,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 233 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 645913433600, 304247303360, 117111644288, 30058081553, 1791493835, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_5 : availableMass (start .two6wider) ⟨35,27,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨35,27,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 657060793995, 138865156599, 7688575551, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_6 : availableMass (start .two6wider) ⟨36,28,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨36,28,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 736879893181, 197311669947, 13965070551, 2508357, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_7 : availableMass (start .two6wider) ⟨36,30,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨36,30,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 754821876792, 210688370070, 13263668934, 116016, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_8 : availableMass (start .two6wider) ⟨37,31,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨37,31,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 416643922315, 47726736137, 310072901, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_9 : availableMass (start .two6wider) ⟨37,42,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨37,42,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588071301539, 143198107042, 1535118347, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_10 : availableMass (start .two6wider) ⟨38,30,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨38,30,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 451970754653, 61794807228, 817864516, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_11 : availableMass (start .two6wider) ⟨61,9,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨61,9,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 222 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 508441345189, 159153881134, 18703709495, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_12 : availableMass (start .two6wider) ⟨61,20,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨61,20,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 178 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 540398366636, 136375309726, 10900692718, 13660215, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_13 : availableMass (start .two6wider) ⟨62,15,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨62,15,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 509777790425, 132292102280, 12366919300, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_14 : availableMass (start .two6wider) ⟨62,24,0⟩ 116 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨62,24,0⟩ 116 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 553346050689, 133029161585, 7728155405, 3179495, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_15 : availableMass (start .two6wider) ⟨63,21,0⟩ 116 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨63,21,0⟩ 116 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 556266959313, 146938020489, 11278506825, 13011427, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_16 : availableMass (start .two6wider) ⟨63,36,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨63,36,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 158 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588249637886, 151665206858, 3270871320, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_17 : availableMass (start .two6wider) ⟨69,49,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨69,49,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 142692660140, 509046174, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_18 : availableMass (start .two6wider) ⟨70,47,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨70,47,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 147202784380, 759742489, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_19 : availableMass (start .two6wider) ⟨74,46,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨74,46,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148296912900, 874803434, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_20 : availableMass (start .two6wider) ⟨77,31,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨77,31,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 563051251096, 113240454508, 2438710470, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_21 : availableMass (start .two6wider) ⟨77,34,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨77,34,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 577128539261, 125278768752, 2280640603, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_22 : availableMass (start .two6wider) ⟨80,45,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨80,45,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148627306188, 966476178, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_23 : availableMass (start .two6wider) ⟨83,35,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨83,35,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 587962428311, 144596802640, 2664265300, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_24 : availableMass (start .two6wider) ⟨84,33,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨84,33,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 577053917271, 124628887557, 2249115244, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_25 : availableMass (start .two6wider) ⟨85,34,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨85,34,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588036633161, 146621921260, 2928631693, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_26 : availableMass (start .two6wider) ⟨87,44,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨87,44,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148490547024, 1031452379, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_27 : availableMass (start .two6wider) ⟨90,3,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨90,3,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 261 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1216317977407, 479125012026, 42668342048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_28 : availableMass (start .two6wider) ⟨90,31,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨90,31,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 577355077924, 127493587175, 2474232339, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_29 : availableMass (start .two6wider) ⟨91,26,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨91,26,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 168 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 564578396121, 121172422174, 2785055667, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_30 : availableMass (start .two6wider) ⟨91,29,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨91,29,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 165 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 577943768799, 133386867050, 3042318542, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_31 : availableMass (start .two6wider) ⟨93,43,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨93,43,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148616301550, 1094026558, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_32 : availableMass (start .two6wider) ⟨98,33,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨98,33,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 587887661711, 142410460253, 2303294291, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_33 : availableMass (start .two6wider) ⟨99,30,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨99,30,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588209961745, 150732730818, 3069510931, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_34 : availableMass (start .two6wider) ⟨100,42,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨100,42,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 154 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148233752680, 1107388156, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_35 : availableMass (start .two6wider) ⟨105,3,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,3,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 273 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 935428604545, 283680409124, 3286042774, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_36 : availableMass (start .two6wider) ⟨105,20,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,20,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 180 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 566665638017, 129453907366, 1549974846, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_37 : availableMass (start .two6wider) ⟨105,25,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,25,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 578414603403, 136178944659, 2129357086, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_38 : availableMass (start .two6wider) ⟨105,29,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,29,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 166 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588201248441, 149876205571, 2600066116, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_39 : availableMass (start .two6wider) ⟨105,41,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,41,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148537409022, 1135811848, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_40 : availableMass (start .two6wider) ⟨107,28,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨107,28,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 167 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588274422286, 151501451416, 2559345970, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_41 : availableMass (start .two6wider) ⟨111,40,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨111,40,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148316927414, 1093865608, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_42 : availableMass (start .two6wider) ⟨114,26,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨114,26,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 170 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 588358300974, 152408942820, 1948535327, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m10_43 : availableMass (start .two6wider) ⟨116,39,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨116,39,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 148407919878, 1037783030, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_0 : availableMass (start .two7) ⟨1,3,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .two7) ⟨1,3,0⟩ 39 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 204 [4518321774336, 3849816668780, 3250457160752, 2652921551098, 2013174724021, 1481762954305, 1052741762669, 715392883513, 458901283237, 272355160241, 144745944925, 64968299689, 21820118933, 4002529057, 123024466, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_1 : availableMass (start .two7) ⟨2,6,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two7) ⟨2,6,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 198 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1326693567523, 829433432811, 474696370323, 238858451419, 97946477187, 27637978443, 3261215731, 11690115, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_2 : availableMass (start .two7) ⟨5,15,0⟩ 83 < layerNeed := by
  rw [mass_eq (start .two7) ⟨5,15,0⟩ 83 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 158 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1465583404938, 836277508833, 306479979237, 68069649481, 3959762125, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_3 : availableMass (start .two7) ⟨9,26,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .two7) ⟨9,26,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 136 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 836634062880, 166047800981, 6391355299, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_4 : availableMass (start .two7) ⟨10,29,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨10,29,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1017532796750, 237579924972, 10492693272, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_5 : availableMass (start .two7) ⟨34,3,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .two7) ⟨34,3,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 224 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2241395523531, 1606274361974, 1011961172766, 599763022598, 328117018670, 160837804182, 67117558334, 21525996326, 4010374198, 89869776, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_6 : availableMass (start .two7) ⟨66,6,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,6,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 205 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1411532941683, 744256533677, 309124160461, 95358000781, 13256584101, 292825, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_7 : availableMass (start .two7) ⟨66,26,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,26,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1007709471814, 226536749932, 13076187304, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_8 : availableMass (start .two7) ⟨68,32,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two7) ⟨68,32,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1072593710128, 234406961844, 7300603084, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_9 : availableMass (start .two7) ⟨69,21,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨69,21,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 146 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 937562299836, 225143248812, 21228165356, 82783834, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_10 : availableMass (start .two7) ⟨70,30,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7) ⟨70,30,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1134168905857, 337555950113, 19292064129, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_11 : availableMass (start .two7) ⟨85,27,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7) ⟨85,27,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 142 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1135132865343, 353536805581, 26105890465, 19946011, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_12 : availableMass (start .two7) ⟨85,42,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨85,42,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 128 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1148494575748, 287199303119, 3687420799, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_13 : availableMass (start .two7) ⟨86,45,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨86,45,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 127 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 330068875284, 3784998704, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_14 : availableMass (start .two7) ⟨98,15,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,15,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 163 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 956034692070, 262418293106, 34366225266, 411024984, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_15 : availableMass (start .two7) ⟨98,17,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,17,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1096836061496, 364693891924, 52958770228, 1516268663, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_16 : availableMass (start .two7) ⟨98,39,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,39,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 360692163150, 8740066093, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_17 : availableMass (start .two7) ⟨99,9,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨99,9,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 996092727216, 347820273116, 67243233922, 834823455, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_18 : availableMass (start .two7) ⟨99,12,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨99,12,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 176 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1050595287821, 361642141826, 66326147918, 1987016739, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_19 : availableMass (start .two7) ⟨107,38,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨107,38,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1148887271841, 301609548828, 6185838052, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_20 : availableMass (start .two7) ⟨115,31,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨115,31,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1150287193844, 346239520321, 15502053789, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m11_21 : availableMass (start .two7) ⟨123,37,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨123,37,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 133 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 359445617868, 9488419484, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_0 : availableMass (start .two7wide) ⟨1,3,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨1,3,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 241 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1299359547006, 909765187739, 605990269839, 380495233379, 220583252759, 114124286379, 49555076639, 15879149939, 2666816679, 61376226, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_1 : availableMass (start .two7wide) ⟨4,12,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨4,12,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 180 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1024548567655, 567729807993, 219286908737, 55542223793, 4966185033, 1461240, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_2 : availableMass (start .two7wide) ⟨12,34,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨12,34,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 460443772934, 45284801822, 6009528, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_3 : availableMass (start .two7wide) ⟨33,6,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨33,6,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 226 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 723752508334, 362514360758, 153107162578, 51069160150, 11279657282, 1024645270, 4198751, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_4 : availableMass (start .two7wide) ⟨37,26,0⟩ 107 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨37,26,0⟩ 107 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 780498482313, 276478129711, 22168683991, 5994115, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_5 : availableMass (start .two7wide) ⟨37,28,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨37,28,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 298622528952, 21467220652, 674534, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_6 : availableMass (start .two7wide) ⟨38,29,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨38,29,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 154 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 332106920898, 24189531810, 1109912, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_7 : availableMass (start .two7wide) ⟨38,37,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨38,37,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 478163181353, 43004776642, 479925, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_8 : availableMass (start .two7wide) ⟨39,32,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨39,32,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 459638174204, 47486730277, 40430392, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_9 : availableMass (start .two7wide) ⟨64,34,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨64,34,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 154 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 479569221066, 47439254748, 24979280, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_10 : availableMass (start .two7wide) ⟨65,9,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,9,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 768643460672, 349391244768, 99460152032, 15545743328, 359145344, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_11 : availableMass (start .two7wide) ⟨65,31,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,31,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 154 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 388152927390, 27899789023, 3009930, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_12 : availableMass (start .two7wide) ⟨65,47,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,47,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 488167268611, 29160197697, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_13 : availableMass (start .two7wide) ⟨67,46,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨67,46,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 146 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 489301101441, 30651668661, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_14 : availableMass (start .two7wide) ⟨70,44,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨70,44,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 491711065769, 33946912559, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_15 : availableMass (start .two7wide) ⟨72,42,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨72,42,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 494280412040, 37687911904, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_16 : availableMass (start .two7wide) ⟨80,23,0⟩ 107 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,23,0⟩ 107 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 780211822651, 269725520024, 23179570928, 77966875, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_17 : availableMass (start .two7wide) ⟨80,26,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,26,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 163 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 465590369946, 60091797980, 635611935, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_18 : availableMass (start .two7wide) ⟨80,41,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,41,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 494671193430, 38763570388, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_19 : availableMass (start .two7wide) ⟨81,24,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨81,24,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 409384218285, 47156548121, 493914236, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_20 : availableMass (start .two7wide) ⟨82,21,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨82,21,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 170 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 451495476954, 70421367584, 2085508844, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_21 : availableMass (start .two7wide) ⟨84,33,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨84,33,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 477822998539, 46451730794, 41550606, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_22 : availableMass (start .two7wide) ⟨88,32,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨88,32,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 479050734442, 48551874120, 73589904, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_23 : availableMass (start .two7wide) ⟨89,31,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨89,31,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 480861911390, 51402793561, 124682437, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_24 : availableMass (start .two7wide) ⟨93,40,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨93,40,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 494385304213, 39092184269, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_25 : availableMass (start .two7wide) ⟨95,3,0⟩ 82 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨95,3,0⟩ 82 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 247 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1317602761131, 708309315737, 221359607965, 10753498346, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_26 : availableMass (start .two7wide) ⟨95,15,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨95,15,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 184 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 379795209463, 63006755971, 2376574670, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_27 : availableMass (start .two7wide) ⟨96,19,0⟩ 110 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨96,19,0⟩ 110 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 173 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 390969730584, 52690074308, 1223264115, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_28 : availableMass (start .two7wide) ⟨101,30,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨101,30,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 158 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 480491059683, 51520343994, 164642265, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_29 : availableMass (start .two7wide) ⟨106,39,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨106,39,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 494061066415, 39278444138, 276369, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_30 : availableMass (start .two7wide) ⟨109,29,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨109,29,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 480870866545, 52439289414, 213413203, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_31 : availableMass (start .two7wide) ⟨111,3,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨111,3,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 259 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1022012359259, 500466381487, 104870491349, 35524866, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_32 : availableMass (start .two7wide) ⟨111,22,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨111,22,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 169 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 467708573745, 64189629170, 1055870859, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_33 : availableMass (start .two7wide) ⟨118,38,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨118,38,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 151 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 493833377794, 39462798933, 1489080, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_34 : availableMass (start .two7wide) ⟨119,20,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨119,20,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 172 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 408942999081, 46544801394, 351913938, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_35 : availableMass (start .two7wide) ⟨119,21,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨119,21,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 468024949508, 64259414620, 922666708, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m12_36 : availableMass (start .two7wide) ⟨120,28,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨120,28,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 161 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 480594826042, 52251547097, 232381005, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m0_0⟩
    · exact ⟨by decide, m0_1⟩
    · exact ⟨by decide, m0_2⟩
    · exact ⟨by decide, m0_3⟩
    · exact ⟨by decide, m0_4⟩
    · exact ⟨by decide, m0_5⟩
    · exact ⟨by decide, m0_6⟩
    · exact ⟨by decide, m0_7⟩
    · exact ⟨by decide, m0_8⟩
    · exact ⟨by decide, m0_9⟩
    · exact ⟨by decide, m0_10⟩
    · exact ⟨by decide, m0_11⟩
    · exact ⟨by decide, m0_12⟩
    · exact ⟨by decide, m0_13⟩
    · exact ⟨by decide, m0_14⟩
    · exact ⟨by decide, m0_15⟩
    · exact ⟨by decide, m0_16⟩
    · exact ⟨by decide, m0_17⟩
    · exact ⟨by decide, m0_18⟩
    · exact ⟨by decide, m0_19⟩
    · exact ⟨by decide, m0_20⟩
    · exact ⟨by decide, m0_21⟩
    · exact ⟨by decide, m0_22⟩
    · exact ⟨by decide, m0_23⟩
    · exact ⟨by decide, m0_24⟩
    · exact ⟨by decide, m0_25⟩
    · exact ⟨by decide, m0_26⟩
    · exact ⟨by decide, m0_27⟩
    · exact ⟨by decide, m0_28⟩
    · exact ⟨by decide, m0_29⟩
    · exact ⟨by decide, m0_30⟩
    · exact ⟨by decide, m0_31⟩
    · exact ⟨by decide, m0_32⟩
    · exact ⟨by decide, m0_33⟩
    · exact ⟨by decide, m0_34⟩
    · exact ⟨by decide, m0_35⟩
    · exact ⟨by decide, m0_36⟩
    · exact ⟨by decide, m0_37⟩
    · exact ⟨by decide, m0_38⟩
    · exact ⟨by decide, m0_39⟩
    · exact ⟨by decide, m0_40⟩
    · exact ⟨by decide, m0_41⟩
    · exact ⟨by decide, m0_42⟩
    · exact ⟨by decide, m0_43⟩
    · exact ⟨by decide, m0_44⟩
    · exact ⟨by decide, m0_45⟩
    · exact ⟨by decide, m0_46⟩
    · exact ⟨by decide, m0_47⟩
    · exact ⟨by decide, m0_48⟩
    · exact ⟨by decide, m0_49⟩
    · exact ⟨by decide, m0_50⟩
    · exact ⟨by decide, m0_51⟩
    · exact ⟨by decide, m0_52⟩
    · exact ⟨by decide, m0_53⟩
    · exact ⟨by decide, m0_54⟩
    · exact ⟨by decide, m0_55⟩
    · exact ⟨by decide, m0_56⟩
    · exact ⟨by decide, m0_57⟩
    · exact ⟨by decide, m0_58⟩
    · exact ⟨by decide, m0_59⟩
    · exact ⟨by decide, m0_60⟩
    · exact ⟨by decide, m0_61⟩
    · exact ⟨by decide, m0_62⟩
    · exact ⟨by decide, m0_63⟩
    · exact ⟨by decide, m0_64⟩
    · exact ⟨by decide, m0_65⟩
    · exact ⟨by decide, m0_66⟩
    · exact ⟨by decide, m0_67⟩
    · exact ⟨by decide, m0_68⟩
    · exact ⟨by decide, m0_69⟩
    · exact ⟨by decide, m0_70⟩
    · exact ⟨by decide, m0_71⟩
    · exact ⟨by decide, m0_72⟩
    · exact ⟨by decide, m0_73⟩
    · exact ⟨by decide, m0_74⟩
    · exact ⟨by decide, m0_75⟩
    · exact ⟨by decide, m0_76⟩
    · exact ⟨by decide, m0_77⟩
    · exact ⟨by decide, m0_78⟩
    · exact ⟨by decide, m0_79⟩
    · exact ⟨by decide, m0_80⟩
    · exact ⟨by decide, m0_81⟩
    · exact ⟨by decide, m0_82⟩
    · exact ⟨by decide, m0_83⟩
    · exact ⟨by decide, m0_84⟩
    · exact ⟨by decide, m0_85⟩
    · exact ⟨by decide, m0_86⟩
    · exact ⟨by decide, m0_87⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
    · exact ⟨by decide, m1_6⟩
    · exact ⟨by decide, m1_7⟩
    · exact ⟨by decide, m1_8⟩
    · exact ⟨by decide, m1_9⟩
    · exact ⟨by decide, m1_10⟩
    · exact ⟨by decide, m1_11⟩
    · exact ⟨by decide, m1_12⟩
    · exact ⟨by decide, m1_13⟩
    · exact ⟨by decide, m1_14⟩
    · exact ⟨by decide, m1_15⟩
    · exact ⟨by decide, m1_16⟩
    · exact ⟨by decide, m1_17⟩
    · exact ⟨by decide, m1_18⟩
    · exact ⟨by decide, m1_19⟩
    · exact ⟨by decide, m1_20⟩
    · exact ⟨by decide, m1_21⟩
    · exact ⟨by decide, m1_22⟩
    · exact ⟨by decide, m1_23⟩
    · exact ⟨by decide, m1_24⟩
    · exact ⟨by decide, m1_25⟩
    · exact ⟨by decide, m1_26⟩
    · exact ⟨by decide, m1_27⟩
    · exact ⟨by decide, m1_28⟩
    · exact ⟨by decide, m1_29⟩
    · exact ⟨by decide, m1_30⟩
    · exact ⟨by decide, m1_31⟩
    · exact ⟨by decide, m1_32⟩
    · exact ⟨by decide, m1_33⟩
    · exact ⟨by decide, m1_34⟩
    · exact ⟨by decide, m1_35⟩
    · exact ⟨by decide, m1_36⟩
    · exact ⟨by decide, m1_37⟩
    · exact ⟨by decide, m1_38⟩
    · exact ⟨by decide, m1_39⟩
    · exact ⟨by decide, m1_40⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩
    · exact ⟨by decide, m2_3⟩
    · exact ⟨by decide, m2_4⟩
    · exact ⟨by decide, m2_5⟩
    · exact ⟨by decide, m2_6⟩
    · exact ⟨by decide, m2_7⟩
    · exact ⟨by decide, m2_8⟩
    · exact ⟨by decide, m2_9⟩
    · exact ⟨by decide, m2_10⟩
    · exact ⟨by decide, m2_11⟩
    · exact ⟨by decide, m2_12⟩
    · exact ⟨by decide, m2_13⟩
    · exact ⟨by decide, m2_14⟩
    · exact ⟨by decide, m2_15⟩
    · exact ⟨by decide, m2_16⟩
    · exact ⟨by decide, m2_17⟩
    · exact ⟨by decide, m2_18⟩
    · exact ⟨by decide, m2_19⟩
    · exact ⟨by decide, m2_20⟩
    · exact ⟨by decide, m2_21⟩
    · exact ⟨by decide, m2_22⟩
    · exact ⟨by decide, m2_23⟩
    · exact ⟨by decide, m2_24⟩
    · exact ⟨by decide, m2_25⟩
    · exact ⟨by decide, m2_26⟩
    · exact ⟨by decide, m2_27⟩
    · exact ⟨by decide, m2_28⟩
    · exact ⟨by decide, m2_29⟩
    · exact ⟨by decide, m2_30⟩
    · exact ⟨by decide, m2_31⟩
    · exact ⟨by decide, m2_32⟩
    · exact ⟨by decide, m2_33⟩
    · exact ⟨by decide, m2_34⟩
    · exact ⟨by decide, m2_35⟩
    · exact ⟨by decide, m2_36⟩
    · exact ⟨by decide, m2_37⟩
    · exact ⟨by decide, m2_38⟩
    · exact ⟨by decide, m2_39⟩
    · exact ⟨by decide, m2_40⟩
    · exact ⟨by decide, m2_41⟩
    · exact ⟨by decide, m2_42⟩
    · exact ⟨by decide, m2_43⟩
    · exact ⟨by decide, m2_44⟩
    · exact ⟨by decide, m2_45⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m3_0⟩
    · exact ⟨by decide, m3_1⟩
    · exact ⟨by decide, m3_2⟩
    · exact ⟨by decide, m3_3⟩
    · exact ⟨by decide, m3_4⟩
    · exact ⟨by decide, m3_5⟩
    · exact ⟨by decide, m3_6⟩
    · exact ⟨by decide, m3_7⟩
    · exact ⟨by decide, m3_8⟩
    · exact ⟨by decide, m3_9⟩
    · exact ⟨by decide, m3_10⟩
    · exact ⟨by decide, m3_11⟩
    · exact ⟨by decide, m3_12⟩
    · exact ⟨by decide, m3_13⟩
    · exact ⟨by decide, m3_14⟩
    · exact ⟨by decide, m3_15⟩
    · exact ⟨by decide, m3_16⟩
    · exact ⟨by decide, m3_17⟩
    · exact ⟨by decide, m3_18⟩
    · exact ⟨by decide, m3_19⟩
    · exact ⟨by decide, m3_20⟩
    · exact ⟨by decide, m3_21⟩
    · exact ⟨by decide, m3_22⟩
    · exact ⟨by decide, m3_23⟩
    · exact ⟨by decide, m3_24⟩
    · exact ⟨by decide, m3_25⟩
    · exact ⟨by decide, m3_26⟩
    · exact ⟨by decide, m3_27⟩
    · exact ⟨by decide, m3_28⟩
    · exact ⟨by decide, m3_29⟩
    · exact ⟨by decide, m3_30⟩
    · exact ⟨by decide, m3_31⟩
    · exact ⟨by decide, m3_32⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m4_0⟩
    · exact ⟨by decide, m4_1⟩
    · exact ⟨by decide, m4_2⟩
    · exact ⟨by decide, m4_3⟩
    · exact ⟨by decide, m4_4⟩
    · exact ⟨by decide, m4_5⟩
    · exact ⟨by decide, m4_6⟩
    · exact ⟨by decide, m4_7⟩
    · exact ⟨by decide, m4_8⟩
    · exact ⟨by decide, m4_9⟩
    · exact ⟨by decide, m4_10⟩
    · exact ⟨by decide, m4_11⟩
    · exact ⟨by decide, m4_12⟩
    · exact ⟨by decide, m4_13⟩
    · exact ⟨by decide, m4_14⟩
    · exact ⟨by decide, m4_15⟩
    · exact ⟨by decide, m4_16⟩
    · exact ⟨by decide, m4_17⟩
    · exact ⟨by decide, m4_18⟩
    · exact ⟨by decide, m4_19⟩
    · exact ⟨by decide, m4_20⟩
    · exact ⟨by decide, m4_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m5_0⟩
    · exact ⟨by decide, m5_1⟩
    · exact ⟨by decide, m5_2⟩
    · exact ⟨by decide, m5_3⟩
    · exact ⟨by decide, m5_4⟩
    · exact ⟨by decide, m5_5⟩
    · exact ⟨by decide, m5_6⟩
    · exact ⟨by decide, m5_7⟩
    · exact ⟨by decide, m5_8⟩
    · exact ⟨by decide, m5_9⟩
    · exact ⟨by decide, m5_10⟩
    · exact ⟨by decide, m5_11⟩
    · exact ⟨by decide, m5_12⟩
    · exact ⟨by decide, m5_13⟩
    · exact ⟨by decide, m5_14⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m6_0⟩
    · exact ⟨by decide, m6_1⟩
    · exact ⟨by decide, m6_2⟩
    · exact ⟨by decide, m6_3⟩
    · exact ⟨by decide, m6_4⟩
    · exact ⟨by decide, m6_5⟩
    · exact ⟨by decide, m6_6⟩
    · exact ⟨by decide, m6_7⟩
    · exact ⟨by decide, m6_8⟩
    · exact ⟨by decide, m6_9⟩
    · exact ⟨by decide, m6_10⟩
    · exact ⟨by decide, m6_11⟩
    · exact ⟨by decide, m6_12⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m7_0⟩
    · exact ⟨by decide, m7_1⟩
    · exact ⟨by decide, m7_2⟩
    · exact ⟨by decide, m7_3⟩
    · exact ⟨by decide, m7_4⟩
    · exact ⟨by decide, m7_5⟩
    · exact ⟨by decide, m7_6⟩
    · exact ⟨by decide, m7_7⟩
    · exact ⟨by decide, m7_8⟩
    · exact ⟨by decide, m7_9⟩
    · exact ⟨by decide, m7_10⟩
    · exact ⟨by decide, m7_11⟩
    · exact ⟨by decide, m7_12⟩
    · exact ⟨by decide, m7_13⟩
    · exact ⟨by decide, m7_14⟩
    · exact ⟨by decide, m7_15⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m8_0⟩
    · exact ⟨by decide, m8_1⟩
    · exact ⟨by decide, m8_2⟩
    · exact ⟨by decide, m8_3⟩
    · exact ⟨by decide, m8_4⟩
    · exact ⟨by decide, m8_5⟩
    · exact ⟨by decide, m8_6⟩
    · exact ⟨by decide, m8_7⟩
    · exact ⟨by decide, m8_8⟩
    · exact ⟨by decide, m8_9⟩
    · exact ⟨by decide, m8_10⟩
    · exact ⟨by decide, m8_11⟩
    · exact ⟨by decide, m8_12⟩
    · exact ⟨by decide, m8_13⟩
    · exact ⟨by decide, m8_14⟩
    · exact ⟨by decide, m8_15⟩
    · exact ⟨by decide, m8_16⟩
    · exact ⟨by decide, m8_17⟩
    · exact ⟨by decide, m8_18⟩
    · exact ⟨by decide, m8_19⟩
    · exact ⟨by decide, m8_20⟩
    · exact ⟨by decide, m8_21⟩
    · exact ⟨by decide, m8_22⟩
    · exact ⟨by decide, m8_23⟩
    · exact ⟨by decide, m8_24⟩
    · exact ⟨by decide, m8_25⟩
    · exact ⟨by decide, m8_26⟩
    · exact ⟨by decide, m8_27⟩
    · exact ⟨by decide, m8_28⟩
    · exact ⟨by decide, m8_29⟩
    · exact ⟨by decide, m8_30⟩
    · exact ⟨by decide, m8_31⟩
    · exact ⟨by decide, m8_32⟩
    · exact ⟨by decide, m8_33⟩
    · exact ⟨by decide, m8_34⟩
    · exact ⟨by decide, m8_35⟩
    · exact ⟨by decide, m8_36⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m9_0⟩
    · exact ⟨by decide, m9_1⟩
    · exact ⟨by decide, m9_2⟩
    · exact ⟨by decide, m9_3⟩
    · exact ⟨by decide, m9_4⟩
    · exact ⟨by decide, m9_5⟩
    · exact ⟨by decide, m9_6⟩
    · exact ⟨by decide, m9_7⟩
    · exact ⟨by decide, m9_8⟩
    · exact ⟨by decide, m9_9⟩
    · exact ⟨by decide, m9_10⟩
    · exact ⟨by decide, m9_11⟩
    · exact ⟨by decide, m9_12⟩
    · exact ⟨by decide, m9_13⟩
    · exact ⟨by decide, m9_14⟩
    · exact ⟨by decide, m9_15⟩
    · exact ⟨by decide, m9_16⟩
    · exact ⟨by decide, m9_17⟩
    · exact ⟨by decide, m9_18⟩
    · exact ⟨by decide, m9_19⟩
    · exact ⟨by decide, m9_20⟩
    · exact ⟨by decide, m9_21⟩
    · exact ⟨by decide, m9_22⟩
    · exact ⟨by decide, m9_23⟩
    · exact ⟨by decide, m9_24⟩
    · exact ⟨by decide, m9_25⟩
    · exact ⟨by decide, m9_26⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m10_0⟩
    · exact ⟨by decide, m10_1⟩
    · exact ⟨by decide, m10_2⟩
    · exact ⟨by decide, m10_3⟩
    · exact ⟨by decide, m10_4⟩
    · exact ⟨by decide, m10_5⟩
    · exact ⟨by decide, m10_6⟩
    · exact ⟨by decide, m10_7⟩
    · exact ⟨by decide, m10_8⟩
    · exact ⟨by decide, m10_9⟩
    · exact ⟨by decide, m10_10⟩
    · exact ⟨by decide, m10_11⟩
    · exact ⟨by decide, m10_12⟩
    · exact ⟨by decide, m10_13⟩
    · exact ⟨by decide, m10_14⟩
    · exact ⟨by decide, m10_15⟩
    · exact ⟨by decide, m10_16⟩
    · exact ⟨by decide, m10_17⟩
    · exact ⟨by decide, m10_18⟩
    · exact ⟨by decide, m10_19⟩
    · exact ⟨by decide, m10_20⟩
    · exact ⟨by decide, m10_21⟩
    · exact ⟨by decide, m10_22⟩
    · exact ⟨by decide, m10_23⟩
    · exact ⟨by decide, m10_24⟩
    · exact ⟨by decide, m10_25⟩
    · exact ⟨by decide, m10_26⟩
    · exact ⟨by decide, m10_27⟩
    · exact ⟨by decide, m10_28⟩
    · exact ⟨by decide, m10_29⟩
    · exact ⟨by decide, m10_30⟩
    · exact ⟨by decide, m10_31⟩
    · exact ⟨by decide, m10_32⟩
    · exact ⟨by decide, m10_33⟩
    · exact ⟨by decide, m10_34⟩
    · exact ⟨by decide, m10_35⟩
    · exact ⟨by decide, m10_36⟩
    · exact ⟨by decide, m10_37⟩
    · exact ⟨by decide, m10_38⟩
    · exact ⟨by decide, m10_39⟩
    · exact ⟨by decide, m10_40⟩
    · exact ⟨by decide, m10_41⟩
    · exact ⟨by decide, m10_42⟩
    · exact ⟨by decide, m10_43⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m11_0⟩
    · exact ⟨by decide, m11_1⟩
    · exact ⟨by decide, m11_2⟩
    · exact ⟨by decide, m11_3⟩
    · exact ⟨by decide, m11_4⟩
    · exact ⟨by decide, m11_5⟩
    · exact ⟨by decide, m11_6⟩
    · exact ⟨by decide, m11_7⟩
    · exact ⟨by decide, m11_8⟩
    · exact ⟨by decide, m11_9⟩
    · exact ⟨by decide, m11_10⟩
    · exact ⟨by decide, m11_11⟩
    · exact ⟨by decide, m11_12⟩
    · exact ⟨by decide, m11_13⟩
    · exact ⟨by decide, m11_14⟩
    · exact ⟨by decide, m11_15⟩
    · exact ⟨by decide, m11_16⟩
    · exact ⟨by decide, m11_17⟩
    · exact ⟨by decide, m11_18⟩
    · exact ⟨by decide, m11_19⟩
    · exact ⟨by decide, m11_20⟩
    · exact ⟨by decide, m11_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m12_0⟩
    · exact ⟨by decide, m12_1⟩
    · exact ⟨by decide, m12_2⟩
    · exact ⟨by decide, m12_3⟩
    · exact ⟨by decide, m12_4⟩
    · exact ⟨by decide, m12_5⟩
    · exact ⟨by decide, m12_6⟩
    · exact ⟨by decide, m12_7⟩
    · exact ⟨by decide, m12_8⟩
    · exact ⟨by decide, m12_9⟩
    · exact ⟨by decide, m12_10⟩
    · exact ⟨by decide, m12_11⟩
    · exact ⟨by decide, m12_12⟩
    · exact ⟨by decide, m12_13⟩
    · exact ⟨by decide, m12_14⟩
    · exact ⟨by decide, m12_15⟩
    · exact ⟨by decide, m12_16⟩
    · exact ⟨by decide, m12_17⟩
    · exact ⟨by decide, m12_18⟩
    · exact ⟨by decide, m12_19⟩
    · exact ⟨by decide, m12_20⟩
    · exact ⟨by decide, m12_21⟩
    · exact ⟨by decide, m12_22⟩
    · exact ⟨by decide, m12_23⟩
    · exact ⟨by decide, m12_24⟩
    · exact ⟨by decide, m12_25⟩
    · exact ⟨by decide, m12_26⟩
    · exact ⟨by decide, m12_27⟩
    · exact ⟨by decide, m12_28⟩
    · exact ⟨by decide, m12_29⟩
    · exact ⟨by decide, m12_30⟩
    · exact ⟨by decide, m12_31⟩
    · exact ⟨by decide, m12_32⟩
    · exact ⟨by decide, m12_33⟩
    · exact ⟨by decide, m12_34⟩
    · exact ⟨by decide, m12_35⟩
    · exact ⟨by decide, m12_36⟩

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := by cases k <;> decide
    have hi : 0 < (start k).j + q.j := by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
