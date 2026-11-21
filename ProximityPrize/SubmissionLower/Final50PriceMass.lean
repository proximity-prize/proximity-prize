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
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (_hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  exact (P3_6_8_1.sumBelow_eq (fastLayer r y L) _).symm

private def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 12) = v) &&
        check f (offset + min length 12) (length - 12) vs

private theorem check_sum (f : ℕ → ℕ) (offset length : ℕ) (values : List ℕ)
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

private theorem m0_0 : availableMass (start .empty) ⟨1,9,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨1,9,0⟩ 2 (by decide)]
  exact mass_of_checks _ 185 [4568938228762, 3763116369948, 3044428803120, 2418920096916, 1881638323464, 1427253641292, 1050058295328, 743966616900, 502515023736, 318862019964, 185788196112, 95696229108, 40610882280, 12179005356, 1669534464, 14065080] (by decide +kernel) (by decide)

private theorem m0_1 : availableMass (start .empty) ⟨1,15,0⟩ 9 < layerNeed := by
  rw [mass_eq (start .empty) ⟨1,15,0⟩ 9 (by decide)]
  exact mass_of_checks _ 119 [4826922552889, 3820116248514, 2669151592494, 1764590647194, 1083571583814, 599943325554, 284265547614, 103808677194, 22553893494, 1193287973] (by decide +kernel) (by decide)

private theorem m0_2 : availableMass (start .empty) ⟨1,27,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨1,27,0⟩ 34 (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 4831459599162, 3261679315212, 1577219396664, 587067999132, 129833340600, 6983229411] (by decide +kernel) (by decide)

private theorem m0_3 : availableMass (start .empty) ⟨2,12,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .empty) ⟨2,12,0⟩ 3 (by decide)]
  exact mass_of_checks _ 140 [4535671237641, 3495109692912, 2597751497328, 1863114603504, 1277589891696, 826564951536, 494424082032, 264548291568, 119315297904, 40099528176, 7272118896, 209081376] (by decide +kernel) (by decide)

private theorem m0_4 : availableMass (start .empty) ⟨2,18,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .empty) ⟨2,18,0⟩ 10 (by decide)]
  exact mass_of_checks _ 101 [4848879172827, 3743364319365, 2405735665905, 1419591058941, 740654141097, 318601937397, 97064855265, 13626684525, 124970775] (by decide +kernel) (by decide)

private theorem m0_5 : availableMass (start .empty) ⟨2,29,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨2,29,0⟩ 36 (by decide)]
  exact mass_of_checks _ 92 [4881692334132, 4881692334132, 4881692334132, 3530615278224, 1643837087964, 571284260032, 107986821180, 3384383084] (by decide +kernel) (by decide)

private theorem m0_6 : availableMass (start .empty) ⟨3,9,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 10 (by decide)]
  exact mass_of_checks _ 193 [4866555313648, 4274565471312, 3469991518644, 2771499764184, 2172147095292, 1664854350432, 1242406319172, 897451742184, 622503311244, 409937669232, 251995410132, 140781079032, 68263172124, 26274136704, 6510371172, 532225032, 24238] (by decide +kernel) (by decide)

private theorem m0_7 : availableMass (start .empty) ⟨3,30,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,30,0⟩ 37 (by decide)]
  exact mass_of_checks _ 92 [4881692334132, 4881692334132, 4881692334132, 3687339190621, 1686996413986, 567833964394, 99690745522, 2367013108] (by decide +kernel) (by decide)

private theorem m0_8 : availableMass (start .empty) ⟨4,12,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 22 (by decide)]
  exact mass_of_checks _ 159 [4881692334132, 4860150408740, 4078248937748, 3062964613652, 2229248223764, 1560404633876, 1039308728084, 648405408788, 369709596692, 184806230804, 74850268436, 20566685204, 2250475028, 4628828] (by decide +kernel) (by decide)

private theorem m0_9 : availableMass (start .empty) ⟨4,32,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,32,0⟩ 38 (by decide)]
  exact mass_of_checks _ 89 [4881692334132, 4881692334132, 4881692334132, 3813288660586, 1673296577264, 513832219568, 71719531632, 601241862] (by decide +kernel) (by decide)

private theorem m0_10 : availableMass (start .empty) ⟨7,21,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨7,21,0⟩ 32 (by decide)]
  exact mass_of_checks _ 110 [4881692334132, 4881692334132, 4743269261113, 3244800828659, 1840214716331, 910326952211, 361173207659, 94756396019, 9046672619, 5012037] (by decide +kernel) (by decide)

private theorem m0_11 : availableMass (start .empty) ⟨10,30,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,30,0⟩ 39 (by decide)]
  exact mass_of_checks _ 94 [4881692334132, 4881692334132, 4881692334132, 4024311291825, 1895284999241, 665813815181, 133509652721, 5477515555] (by decide +kernel) (by decide)

private theorem m0_12 : availableMass (start .empty) ⟨12,36,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨12,36,0⟩ 42 (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4393568516688, 1983731303628, 554313284172, 62315765964, 148290372] (by decide +kernel) (by decide)

private theorem m0_13 : availableMass (start .empty) ⟨14,6,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨14,6,0⟩ 1 (by decide)]
  exact mass_of_checks _ 276 [4533921676766, 3791007916751, 3141731239139, 2579658446999, 2096607881963, 1684800993503, 1336862338931, 1045819583399, 805103499899, 608547969263, 450389980163, 325269629111, 228230120459, 154717766399, 100581986963, 62075310023, 35853371291, 18974914319, 8901790499, 3498959063, 1034487083, 179549471, 8428979] (by decide +kernel) (by decide)

private theorem m0_14 : availableMass (start .empty) ⟨18,6,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,6,0⟩ 5 (by decide)]
  exact mass_of_checks _ 280 [4723583907733, 3958963884463, 3233765578675, 2612581360087, 2085002772763, 1641167795839, 1271760843523, 968012765095, 721700844907, 525148802383, 371226792019, 253351403383, 165485661115, 102139024927, 58367389603, 29773084999, 12504888091, 3318028741, 169842118, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_15 : availableMass (start .empty) ⟨25,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨25,3,0⟩ 1 (by decide)]
  exact mass_of_checks _ 551 [4572717010964, 3891857891345, 3272979155489, 2714490577025, 2212756176113, 1764245788721, 1365535066625, 1013305477409, 704344304465, 435804996491, 211704324347, 58658334055, 4707436387, 10656725, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_16 : availableMass (start .empty) ⟨32,3,0⟩ 6 < layerNeed := by
  rw [mass_eq (start .empty) ⟨32,3,0⟩ 6 (by decide)]
  exact mass_of_checks _ 556 [4769349457218, 4045985379030, 3298406730258, 2627164236270, 2027577476010, 1495103197062, 1025335315650, 614185573814, 269061302512, 51929851668, 1367953532, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_17 : availableMass (start .empty) ⟨33,6,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,6,0⟩ 18 (by decide)]
  exact mass_of_checks _ 293 [4881692334132, 4726497233312, 3781159553572, 2873440552228, 2123781080164, 1513835749348, 1026343083940, 645125520292, 355089944499, 143930988805, 22955636671, 181853441, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_18 : availableMass (start .empty) ⟨33,9,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,9,0⟩ 20 (by decide)]
  exact mass_of_checks _ 203 [4881692334132, 4790087392154, 3742303350174, 2664866241474, 1833683898102, 1208748286842, 753543296142, 435044736114, 223720338534, 93529805948, 22698505600, 621949707, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_19 : availableMass (start .empty) ⟨36,18,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨36,18,0⟩ 35 (by decide)]
  exact mass_of_checks _ 126 [4881692334132, 4881692334132, 4867260778230, 3589658624799, 2023925405427, 1035634081383, 462058415739, 167319153711, 42384022659, 5067732087, 55478871] (by decide +kernel) (by decide)

private theorem m0_20 : availableMass (start .empty) ⟨39,33,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨39,33,0⟩ 45 (by decide)]
  exact mass_of_checks _ 95 [4881692334132, 4881692334132, 4881692334132, 4732355242419, 2499644780224, 811303531612, 155133009664, 7112043840] (by decide +kernel) (by decide)

private theorem m0_21 : availableMass (start .empty) ⟨47,3,0⟩ 9 < layerNeed := by
  rw [mass_eq (start .empty) ⟨47,3,0⟩ 9 (by decide)]
  exact mass_of_checks _ 559 [4840905597120, 4042937393439, 3047958044151, 2161909449231, 1377916489383, 690737337562, 165008747242, 3863238762, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_22 : availableMass (start .empty) ⟨48,6,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .empty) ⟨48,6,0⟩ 24 (by decide)]
  exact mass_of_checks _ 299 [4881692334132, 4881692334132, 4166277123349, 2969240276593, 1997142777325, 1222937147017, 621215195651, 182905733105, 7497491728, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_23 : availableMass (start .empty) ⟨62,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .empty) ⟨62,3,0⟩ 11 (by decide)]
  exact mass_of_checks _ 561 [4874050239971, 4058556876111, 2811721765719, 1706752791831, 738405296107, 90871716472, 41176380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_24 : availableMass (start .empty) ⟨62,15,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨62,15,0⟩ 32 (by decide)]
  exact mass_of_checks _ 142 [4881692334132, 4881692334132, 4718257223955, 3021330754001, 1556015745521, 678920024081, 212725763106, 20958756015, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_25 : availableMass (start .empty) ⟨62,27,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨62,27,0⟩ 36 (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 3230355754950, 1242765452634, 355872720894, 58772384754, 2593504374, 1607] (by decide +kernel) (by decide)

private theorem m0_26 : availableMass (start .empty) ⟨63,6,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .empty) ⟨63,6,0⟩ 30 (by decide)]
  exact mass_of_checks _ 305 [4881692334132, 4881692334132, 4651050608282, 3294615403642, 2040164602258, 1050080165330, 306983089092, 8644569552, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_27 : availableMass (start .empty) ⟨63,29,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨63,29,0⟩ 37 (by decide)]
  exact mass_of_checks _ 93 [4881692334132, 4881692334132, 4881692334132, 3396998770994, 1247472480911, 328607538279, 45224080439, 1104707064] (by decide +kernel) (by decide)

private theorem m0_28 : availableMass (start .empty) ⟨64,32,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,32,0⟩ 40 (by decide)]
  exact mass_of_checks _ 91 [4881692334132, 4881692334132, 4881692334132, 3975754594666, 1489344601176, 371092403544, 44339842648, 589371720] (by decide +kernel) (by decide)

private theorem m0_29 : availableMass (start .empty) ⟨65,21,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,21,0⟩ 39 (by decide)]
  exact mass_of_checks _ 117 [4881692334132, 4881692334132, 4881692334132, 4010572796313, 1913546861832, 745873336884, 213503947752, 31060993662, 180845681, 0] (by decide +kernel) (by decide)

private theorem m0_30 : availableMass (start .empty) ⟨65,36,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,36,0⟩ 47 (by decide)]
  exact mass_of_checks _ 92 [4881692334132, 4881692334132, 4881692334132, 4852008373926, 2655400550550, 716552137590, 100475020374, 2201304132] (by decide +kernel) (by decide)

private theorem m0_31 : availableMass (start .empty) ⟨66,27,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,27,0⟩ 43 (by decide)]
  exact mass_of_checks _ 104 [4881692334132, 4881692334132, 4881692334132, 4525485498084, 2193595878669, 739819696677, 167987755509, 16826273277, 147357963] (by decide +kernel) (by decide)

private theorem m0_32 : availableMass (start .empty) ⟨78,3,0⟩ 14 < layerNeed := by
  rw [mass_eq (start .empty) ⟨78,3,0⟩ 14 (by decide)]
  exact mass_of_checks _ 564 [4881692334132, 4272977620288, 2748038584306, 1385578444101, 287723640154, 902114101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_33 : availableMass (start .empty) ⟨78,6,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨78,6,0⟩ 36 (by decide)]
  exact mass_of_checks _ 311 [4881692334132, 4881692334132, 4881692334132, 3898189982599, 2295013460443, 1031451423347, 162828471024, 64445436, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_34 : availableMass (start .empty) ⟨93,3,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .empty) ⟨93,3,0⟩ 16 (by decide)]
  exact mass_of_checks _ 566 [4881692334132, 4418004895870, 2690964623611, 1087873293076, 76206371127, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_35 : availableMass (start .empty) ⟨93,9,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨93,9,0⟩ 40 (by decide)]
  exact mass_of_checks _ 223 [4881692334132, 4881692334132, 4881692334132, 4299954516220, 2342368843422, 871966684660, 68078260111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_36 : availableMass (start .empty) ⟨93,15,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨93,15,0⟩ 43 (by decide)]
  exact mass_of_checks _ 153 [4881692334132, 4881692334132, 4881692334132, 4584353280797, 2496611831026, 935218312006, 138704504210, 5775565, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_37 : availableMass (start .empty) ⟨93,30,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨93,30,0⟩ 45 (by decide)]
  exact mass_of_checks _ 100 [4881692334132, 4881692334132, 4881692334132, 4707679028755, 2228969345704, 576690622072, 70988978480, 309767028, 0] (by decide +kernel) (by decide)

private theorem m0_38 : availableMass (start .empty) ⟨94,22,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,22,0⟩ 44 (by decide)]
  exact mass_of_checks _ 119 [4881692334132, 4881692334132, 4881692334132, 4640168460087, 2343341604227, 748025560919, 108744705333, 28461305, 0, 0] (by decide +kernel) (by decide)

private theorem m0_39 : availableMass (start .empty) ⟨94,32,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,32,0⟩ 46 (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4789940613770, 2371038107508, 589535130772, 68893288884, 453782043, 0] (by decide +kernel) (by decide)

private theorem m0_40 : availableMass (start .empty) ⟨94,43,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,43,0⟩ 49 (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2864763202753, 547268811690, 35434962510, 22511282] (by decide +kernel) (by decide)

private theorem m0_41 : availableMass (start .empty) ⟨95,33,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨95,33,0⟩ 47 (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4850401888506, 2573012324855, 638074733159, 75126781055, 662027794, 0] (by decide +kernel) (by decide)

private theorem m0_42 : availableMass (start .empty) ⟨96,36,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨96,36,0⟩ 48 (by decide)]
  exact mass_of_checks _ 93 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2741371883604, 634058513748, 65507239764, 532899578] (by decide +kernel) (by decide)

private theorem m0_43 : availableMass (start .empty) ⟨102,47,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .empty) ⟨102,47,0⟩ 50 (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 3046192538777, 515251817113, 23056358305, 7050] (by decide +kernel) (by decide)

private theorem m0_44 : availableMass (start .empty) ⟨108,3,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .empty) ⟨108,3,0⟩ 18 (by decide)]
  exact mass_of_checks _ 568 [4881692334132, 4573614600122, 2716549058566, 873302389114, 14615902590, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_45 : availableMass (start .empty) ⟨108,46,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .empty) ⟨108,46,0⟩ 50 (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 3044603737820, 514744602787, 23474700687, 489643] (by decide +kernel) (by decide)

private theorem m0_46 : availableMass (start .empty) ⟨109,39,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .empty) ⟨109,39,0⟩ 49 (by decide)]
  exact mass_of_checks _ 91 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2894739187475, 576807261428, 40469515451, 2793627] (by decide +kernel) (by decide)

private theorem m0_47 : availableMass (start .empty) ⟨116,44,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,44,0⟩ 50 (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 3055148663056, 525356571036, 24718546046, 0] (by decide +kernel) (by decide)

private theorem m0_48 : availableMass (start .empty) ⟨120,43,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .empty) ⟨120,43,0⟩ 50 (by decide)]
  exact mass_of_checks _ 88 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 3060004314089, 528957183490, 24305067206, 0] (by decide +kernel) (by decide)

private theorem m1_0 : availableMass (start .one) ⟨1,9,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .one) ⟨1,9,0⟩ 2 (by decide)]
  exact mass_of_checks _ 139 [4416069346931, 3372582946326, 2496548606694, 1781535154614, 1213814030982, 778653386070, 460318079526, 242069680374, 106166467014, 33863427222, 5412258150, 93823898] (by decide +kernel) (by decide)

private theorem m1_1 : availableMass (start .one) ⟨1,15,0⟩ 9 < layerNeed := by
  rw [mass_eq (start .one) ⟨1,15,0⟩ 9 (by decide)]
  exact mass_of_checks _ 100 [4681131389983, 3427533067863, 2168846984091, 1252225380351, 632253119619, 257468447271, 70362991083, 7381761231, 9683904] (by decide +kernel) (by decide)

private theorem m1_2 : availableMass (start .one) ⟨1,26,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .one) ⟨1,26,0⟩ 35 (by decide)]
  exact mass_of_checks _ 91 [4740005313959, 4439709210263, 4136526561088, 2674349755910, 1135576391362, 330902859094, 40107832514, 144841468] (by decide +kernel) (by decide)

private theorem m1_3 : availableMass (start .one) ⟨2,6,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one) ⟨2,6,0⟩ 11 (by decide)]
  exact mass_of_checks _ 194 [4735842229374, 4086252931992, 3305845855932, 2629989821472, 2051711482884, 1563901445544, 1159314265932, 830568451632, 570146461332, 370394704824, 223523543004, 121607287872, 56584202532, 20256501192, 4290349164, 215918294, 0] (by decide +kernel) (by decide)

private theorem m1_4 : availableMass (start .one) ⟨2,27,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one) ⟨2,27,0⟩ 38 (by decide)]
  exact mass_of_checks _ 93 [4740005313959, 4439709210263, 4152103344383, 3091081841285, 1344208141978, 406862605762, 54682470826, 373312895] (by decide +kernel) (by decide)

private theorem m1_5 : availableMass (start .one) ⟨3,9,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one) ⟨3,9,0⟩ 25 (by decide)]
  exact mass_of_checks _ 162 [4740005313959, 4439709210263, 3784414357772, 2819928710348, 2032531855244, 1405412204876, 921328189964, 562608259532, 311150880908, 148424539724, 55467739916, 12889003724, 866871692, 0] (by decide +kernel) (by decide)

private theorem m1_6 : availableMass (start .one) ⟨4,12,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one) ⟨4,12,0⟩ 40 (by decide)]
  exact mass_of_checks _ 150 [4740005313959, 4439709210263, 4152103344383, 3622392136873, 2517202164488, 1632707495348, 982121553608, 531148291268, 244441900328, 85606812788, 17197700648, 721399815, 0] (by decide +kernel) (by decide)

private theorem m1_7 : availableMass (start .one) ⟨7,21,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one) ⟨7,21,0⟩ 48 (by decide)]
  exact mass_of_checks _ 116 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2751701664488, 1366145661992, 544805823848, 144231497384, 14092322792, 9979604] (by decide +kernel) (by decide)

private theorem m1_8 : availableMass (start .one) ⟨9,27,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one) ⟨9,27,0⟩ 52 (by decide)]
  exact mass_of_checks _ 107 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3097613020431, 1368038056445, 414843504065, 58206586085, 546823300] (by decide +kernel) (by decide)

private theorem m1_9 : availableMass (start .one) ⟨17,3,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one) ⟨17,3,0⟩ 5 (by decide)]
  exact mass_of_checks _ 280 [4629821325071, 3849174507937, 3139861484749, 2532965125081, 2018160953797, 1585670930833, 1226263451197, 931253344969, 692501877301, 502416748417, 353952093613, 240608483257, 156432922789, 96018852721, 54506148637, 27581121193, 11476517844, 3016409215, 149476240, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_10 : availableMass (start .one) ⟨32,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one) ⟨32,3,0⟩ 25 (by decide)]
  exact mass_of_checks _ 300 [4740005313959, 4439709210263, 3821366734024, 2924841420616, 2183752719112, 1579962767368, 1096417615432, 717147225544, 427265472136, 212990045347, 65938098949, 4195954964, 31465, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_11 : availableMass (start .one) ⟨47,3,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .one) ⟨47,3,0⟩ 34 (by decide)]
  exact mass_of_checks _ 309 [4740005313959, 4439709210263, 4132329744725, 3257750633677, 2283466094089, 1503626452261, 893167669537, 428674698601, 104791085779, 1857992032, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_12 : availableMass (start .one) ⟨62,3,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one) ⟨62,3,0⟩ 43 (by decide)]
  exact mass_of_checks _ 318 [4740005313959, 4439709210263, 4152103344383, 3763329589191, 2662391834362, 1648439400754, 860669513002, 273423323263, 10095889828, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_13 : availableMass (start .one) ⟨64,18,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one) ⟨64,18,0⟩ 49 (by decide)]
  exact mass_of_checks _ 127 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2713481718429, 1167619391805, 400434023037, 92273147805, 8565307439, 766480, 0] (by decide +kernel) (by decide)

private theorem m1_14 : availableMass (start .one) ⟨64,32,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one) ⟨64,32,0⟩ 58 (by decide)]
  exact mass_of_checks _ 105 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3547160553433, 1653663022679, 372823315839, 33486007199, 78616103] (by decide +kernel) (by decide)

private theorem m1_15 : availableMass (start .one) ⟨92,6,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one) ⟨92,6,0⟩ 46 (by decide)]
  exact mass_of_checks _ 229 [4740005313959, 4439709210263, 4152103344383, 3840678252367, 2524710442494, 1159968748674, 263935915239, 750563196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_16 : availableMass (start .one) ⟨92,26,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one) ⟨92,26,0⟩ 51 (by decide)]
  exact mass_of_checks _ 107 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2756828849995, 841628230399, 146925839687, 6253969304, 0] (by decide +kernel) (by decide)

private theorem m1_17 : availableMass (start .one) ⟨92,27,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one) ⟨92,27,0⟩ 54 (by decide)]
  exact mass_of_checks _ 109 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3183706435218, 1123547740900, 219924123892, 14274889877, 0, 0] (by decide +kernel) (by decide)

private theorem m1_18 : availableMass (start .one) ⟨92,37,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one) ⟨92,37,0⟩ 59 (by decide)]
  exact mass_of_checks _ 100 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3586378113773, 1586448989244, 247166746588, 9031867008, 0] (by decide +kernel) (by decide)

private theorem m1_19 : availableMass (start .one) ⟨92,38,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one) ⟨92,38,0⟩ 60 (by decide)]
  exact mass_of_checks _ 100 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3613962830135, 1760179189582, 278535248962, 10526970470, 0] (by decide +kernel) (by decide)

private theorem m1_20 : availableMass (start .one) ⟨93,39,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one) ⟨93,39,0⟩ 61 (by decide)]
  exact mass_of_checks _ 100 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3613962830135, 1953459328989, 312641104881, 12143729829, 0] (by decide +kernel) (by decide)

private theorem m1_21 : availableMass (start .one) ⟨94,21,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one) ⟨94,21,0⟩ 55 (by decide)]
  exact mass_of_checks _ 123 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3338971348154, 1427979153560, 372168789080, 37695445457, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_22 : availableMass (start .one) ⟨94,24,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one) ⟨94,24,0⟩ 58 (by decide)]
  exact mass_of_checks _ 119 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3551914960811, 1746783200475, 455076556227, 56006073064, 165794666, 0] (by decide +kernel) (by decide)

private theorem m2_0 : availableMass (start .two) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .two) ⟨1,3,0⟩ 25 (by decide)]
  exact mass_of_checks _ 208 [4577344072499, 4003054728023, 3366791307861, 2682487153221, 2096347002909, 1601272799709, 1190030437509, 855249761301, 589424567181, 384912602349, 233935565109, 128579104869, 60792822141, 22390268541, 5048946789, 310310709, 0, 0] (by decide +kernel) (by decide)

private theorem m2_1 : availableMass (start .two) ⟨1,24,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .two) ⟨1,24,0⟩ 60 (by decide)]
  exact mass_of_checks _ 115 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1524775181542, 495564099550, 79760254678, 1317405376, 0] (by decide +kernel) (by decide)

private theorem m2_2 : availableMass (start .two) ⟨2,6,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .two) ⟨2,6,0⟩ 48 (by decide)]
  exact mass_of_checks _ 185 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2356295261492, 1661150503604, 1116637475636, 705272743604, 409142891828, 209904522932, 88784257844, 26578735796, 3654614324, 31891402, 0, 0] (by decide +kernel) (by decide)

private theorem m2_3 : availableMass (start .two) ⟨2,26,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two) ⟨2,26,0⟩ 62 (by decide)]
  exact mass_of_checks _ 113 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1673833415844, 525784065424, 76335388816, 780459112, 0] (by decide +kernel) (by decide)

private theorem m2_4 : availableMass (start .two) ⟨3,27,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .two) ⟨3,27,0⟩ 64 (by decide)]
  exact mass_of_checks _ 114 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1828729553885, 602295224360, 91061665268, 1139238016, 0] (by decide +kernel) (by decide)

private theorem m2_5 : availableMass (start .two) ⟨4,12,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .two) ⟨4,12,0⟩ 66 (by decide)]
  exact mass_of_checks _ 157 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2078109449434, 1236119571567, 620159220603, 252244055079, 69709281651, 7713324639, 17052237, 0, 0] (by decide +kernel) (by decide)

private theorem m2_6 : availableMass (start .two) ⟨6,18,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two) ⟨6,18,0⟩ 79 (by decide)]
  exact mass_of_checks _ 147 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1735750384073, 843751828688, 277184644592, 47668671248, 1120343040, 0, 0] (by decide +kernel) (by decide)

private theorem m2_7 : availableMass (start .two) ⟨8,24,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .two) ⟨8,24,0⟩ 86 (by decide)]
  exact mass_of_checks _ 141 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 1146834983193, 321837754235, 36031408655, 84435245, 0] (by decide +kernel) (by decide)

private theorem m2_8 : availableMass (start .two) ⟨31,3,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .two) ⟨31,3,0⟩ 52 (by decide)]
  exact mass_of_checks _ 235 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2453544850597, 1711020073794, 1138350781302, 722283437562, 431441555982, 237940571634, 117387841254, 48882643242, 15016177662, 1971687490, 252960, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m2_9 : availableMass (start .two) ⟨33,9,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two) ⟨33,9,0⟩ 74 (by decide)]
  exact mass_of_checks _ 184 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1592633557989, 857197900739, 408540807299, 163367772059, 48961531019, 8351220179, 312618070, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m2_10 : availableMass (start .two) ⟨61,3,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .two) ⟨61,3,0⟩ 66 (by decide)]
  exact mass_of_checks _ 249 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2088683457025, 1297185738072, 701433238812, 315759309504, 88000214322, 2219144462, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m2_11 : availableMass (start .two) ⟨63,15,0⟩ 83 < layerNeed := by
  rw [mass_eq (start .two) ⟨63,15,0⟩ 83 (by decide)]
  exact mass_of_checks _ 161 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1821315286979, 991136033223, 326391315855, 70785828735, 6311355927, 30256257, 0, 0] (by decide +kernel) (by decide)

private theorem m2_12 : availableMass (start .two) ⟨64,32,0⟩ 89 < layerNeed := by
  rw [mass_eq (start .two) ⟨64,32,0⟩ 89 (by decide)]
  exact mass_of_checks _ 132 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 1233735321217, 234526402763, 8500466884, 0] (by decide +kernel) (by decide)

private theorem m2_13 : availableMass (start .two) ⟨91,24,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two) ⟨91,24,0⟩ 88 (by decide)]
  exact mass_of_checks _ 143 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 1196899933913, 268308192724, 22319391220, 77181770, 0] (by decide +kernel) (by decide)

private theorem m2_14 : availableMass (start .two) ⟨92,6,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .two) ⟨92,6,0⟩ 71 (by decide)]
  exact mass_of_checks _ 208 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2170795762323, 1319764745042, 533021687234, 117329949479, 421523906, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m2_15 : availableMass (start .two) ⟨107,39,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two) ⟨107,39,0⟩ 90 (by decide)]
  exact mass_of_checks _ 126 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 1248809202907, 168336881589, 1495917897, 0] (by decide +kernel) (by decide)

private theorem m2_16 : availableMass (start .two) ⟨107,41,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .two) ⟨107,41,0⟩ 91 (by decide)]
  exact mass_of_checks _ 126 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1829003555243, 1314091962201, 192040382718, 1619549780, 0] (by decide +kernel) (by decide)

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hi : 0 < (start k).j + q.j := by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
