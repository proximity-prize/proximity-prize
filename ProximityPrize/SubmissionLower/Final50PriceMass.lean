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

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

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

private theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 6 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 6 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 189 [4760406701472, 3994164254364, 3225714093312, 2561046876132, 1993174140552, 1514971375404, 1119178020624, 798397467252, 545097057432, 351608084412, 210125792544, 112709377284, 51281985192, 17630713932, 3406612272, 125643554] (by decide +kernel) (by decide +kernel)

private theorem m0_1 : availableMass (start .empty) ⟨4,10,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,10,0⟩ 11 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 176 [4876540727652, 4281249530835, 3385262905623, 2622963044731, 1983889384959, 1457484595107, 1033094575975, 699968460363, 447258613071, 264020630899, 139213342647, 61698809115, 20242323103, 3512409411, 87504630] (by decide +kernel) (by decide +kernel)

private theorem m0_2 : availableMass (start .empty) ⟨4,12,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 13 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 150 [4881692334132, 4360203959615, 3299120995004, 2421560994236, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822] (by decide +kernel) (by decide +kernel)

private theorem m0_3 : availableMass (start .empty) ⟨10,8,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,8,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 207 [4481029937559, 3640464436340, 2918998271444, 2307125067060, 1793724797588, 1368215356916, 1020552558420, 741230134964, 521279738900, 352270942068, 226311235796, 136046030900, 74658657684, 35870365940, 13940324948, 3665623476, 381269780, 677332] (by decide +kernel) (by decide +kernel)

private theorem m0_4 : availableMass (start .empty) ⟨11,7,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨11,7,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 236 [4515035343037, 3736804715014, 3060712102274, 2479371591790, 1983689043850, 1565013661334, 1215137989714, 926297917054, 691172674010, 502884833830, 355000312354, 241528368014, 156921601834, 96075957430, 54330721010, 27468521374, 11715329914, 3740460614, 656570050, 20021810] (by decide +kernel) (by decide +kernel)

private theorem m0_5 : availableMass (start .empty) ⟨5,15,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 135 [4881692334132, 4881692334132, 4233093296021, 2962717899758, 1970888744618, 1226948511878, 697038553538, 346250461598, 138626068058, 37157444918, 3786904178, 4206661] (by decide +kernel) (by decide +kernel)

private theorem m0_6 : availableMass (start .empty) ⟨6,18,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .empty) ⟨6,18,0⟩ 29 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 120 [4881692334132, 4881692334132, 4549428548061, 3091617880119, 1897338648771, 1055530108719, 507336835707, 191726623143, 45490482099, 3242641311] (by decide +kernel) (by decide +kernel)

private theorem m0_7 : availableMass (start .empty) ⟨18,6,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,6,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 277 [4566984148934, 3767323230229, 3069134122153, 2472305759005, 1966566293617, 1542190313893, 1189998842809, 901359338413, 668185693825, 482938237237, 338623731913, 228795376189, 147552803473, 89542082245, 49955716057, 24532643533, 9558767068, 2015546530, 38939808, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_8 : availableMass (start .empty) ⟨8,24,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨8,24,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 104 [4881692334132, 4881692334132, 4881692334132, 3699007886408, 1979699715464, 893753145032, 301157376008, 55021902152, 1630544496] (by decide +kernel) (by decide +kernel)

private theorem m0_9 : availableMass (start .empty) ⟨33,5,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,5,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 332 [4504502950141, 3559928801843, 2743760456251, 2054539439779, 1479528390827, 1006626715795, 624370589083, 322210488032, 102564992101, 7823285650, 2817771, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_10 : availableMass (start .empty) ⟨33,6,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,6,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 280 [4673654490223, 3699012357088, 2805192124720, 2067861239872, 1468764640528, 990731176864, 617673611248, 334590924495, 129909255349, 18058545268, 85136106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_11 : availableMass (start .empty) ⟨34,9,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,9,0⟩ 11 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 194 [4873511602989, 4045445684313, 2888719819881, 1993801266393, 1318677368937, 824948326617, 477827192553, 246139873881, 102325529791, 23690275878, 508438598, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_12 : availableMass (start .empty) ⟨13,39,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨13,39,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4501740784363, 2001104563424, 493624585004, 38785923896, 353064] (by decide +kernel) (by decide +kernel)

private theorem m0_13 : availableMass (start .empty) ⟨64,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,4,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 413 [4225915777679, 2878453898060, 1724322516876, 751110702256, 98293374306, 45036300, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_14 : availableMass (start .empty) ⟨64,5,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,5,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 335 [4587136757631, 3233285439930, 2002970451134, 998257577633, 239025956376, 2711602236, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_15 : availableMass (start .empty) ⟨64,6,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,6,0⟩ 10 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 285 [4850061449964, 3766241377563, 2402849269383, 1319406196371, 484736593350, 35611387356, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_16 : availableMass (start .empty) ⟨65,7,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,7,0⟩ 11 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 246 [4871010467695, 3836635043804, 2401219851016, 1296841924564, 477657144068, 37434125479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_17 : availableMass (start .empty) ⟨65,9,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,9,0⟩ 22 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 205 [4881692334132, 4843827486638, 3601360129524, 2139502526952, 1087899257004, 371703125912, 24404435692, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_18 : availableMass (start .empty) ⟨65,10,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,10,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 188 [4881692334132, 4869018683879, 3698711251436, 2168503417956, 1096989792476, 391096458647, 34270888409, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_19 : availableMass (start .empty) ⟨65,12,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,12,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 162 [4881692334132, 4881692334132, 3933865891965, 2244384632442, 1115976711162, 417867612063, 56783425077, 7410145, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_20 : availableMass (start .empty) ⟨66,16,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,16,0⟩ 28 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 131 [4881692334132, 4881692334132, 4270260523624, 2336674312324, 1077742763876, 386723058244, 69776631821, 228917952, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_21 : availableMass (start .empty) ⟨66,18,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,18,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 122 [4881692334132, 4881692334132, 4603665181059, 2655931399533, 1207495609209, 437425158501, 96689710177, 2688086164, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_22 : availableMass (start .empty) ⟨67,20,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,20,0⟩ 33 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 115 [4881692334132, 4881692334132, 4761596049526, 2877109895548, 1261501213132, 437887518236, 95530439344, 4109170360, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_23 : availableMass (start .empty) ⟨66,22,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,22,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 109 [4881692334132, 4881692334132, 4818404075002, 2979123872053, 1259058609577, 417348427517, 88301480497, 5470415431, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_24 : availableMass (start .empty) ⟨66,24,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,24,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 105 [4881692334132, 4881692334132, 4881692334132, 3533552333947, 1478634099256, 485149885048, 103557479608, 8295652222, 367290] (by decide +kernel) (by decide +kernel)

private theorem m0_25 : availableMass (start .empty) ⟨67,28,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,28,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 3843441802681, 1515722001092, 435001707124, 72340660516, 3304542932, 81640] (by decide +kernel) (by decide +kernel)

private theorem m0_26 : availableMass (start .empty) ⟨68,27,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,27,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 100 [4881692334132, 4881692334132, 4881692334132, 3861506030295, 1556518618353, 463838073825, 83090521497, 4602502425, 567127] (by decide +kernel) (by decide +kernel)

private theorem m0_27 : availableMass (start .empty) ⟨68,30,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,30,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4350628907031, 1863364542891, 533340476439, 87945494307, 3850130895, 273] (by decide +kernel) (by decide +kernel)

private theorem m0_28 : availableMass (start .empty) ⟨68,33,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,33,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 93 [4881692334132, 4881692334132, 4881692334132, 4471844931148, 1903273282619, 493537267475, 65114955899, 1318411391] (by decide +kernel) (by decide +kernel)

private theorem m0_29 : availableMass (start .empty) ⟨69,45,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,45,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4670256036170, 1840238971197, 287797064397, 8433090472] (by decide +kernel) (by decide +kernel)

private theorem m0_30 : availableMass (start .empty) ⟨71,43,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,43,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4676000475448, 1898478170869, 327058849413, 13712009859] (by decide +kernel) (by decide +kernel)

private theorem m0_31 : availableMass (start .empty) ⟨69,49,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,49,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4767142719814, 1948447821502, 264470451418, 4356438595] (by decide +kernel) (by decide +kernel)

private theorem m0_32 : availableMass (start .empty) ⟨97,28,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,28,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 100 [4881692334132, 4881692334132, 4881692334132, 4312462679176, 1702266922864, 397852379936, 30329788309, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_33 : availableMass (start .empty) ⟨98,31,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,31,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4584396315773, 1946490016907, 442900915515, 37805032835, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_34 : availableMass (start .empty) ⟨84,46,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨84,46,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4767701568296, 1967869354131, 288312128863, 7858195951] (by decide +kernel) (by decide +kernel)

private theorem m0_35 : availableMass (start .empty) ⟨97,36,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,36,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 89 [4881692334132, 4881692334132, 4881692334132, 4557525757242, 1771970663622, 332864143878, 20346830962, 82251] (by decide +kernel) (by decide +kernel)

private theorem m0_36 : availableMass (start .empty) ⟨97,37,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,37,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 89 [4881692334132, 4881692334132, 4881692334132, 4680466787974, 1949724425383, 371158753327, 23882157599, 8105669] (by decide +kernel) (by decide +kernel)

private theorem m0_37 : availableMass (start .empty) ⟨98,44,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,44,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4766722780194, 1955926011844, 287396054372, 9052704568] (by decide +kernel) (by decide +kernel)

private theorem m0_38 : availableMass (start .empty) ⟨105,43,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,43,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4766216434404, 1948074393032, 283574855044, 8880748792] (by decide +kernel) (by decide +kernel)

private theorem m0_39 : availableMass (start .empty) ⟨98,52,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,52,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 78 [4881692334132, 4881692334132, 4881692334132, 4837998879897, 1999837077020, 214804089148, 1924648282] (by decide +kernel) (by decide +kernel)

private theorem m0_40 : availableMass (start .empty) ⟨112,41,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨112,41,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 86 [4881692334132, 4881692334132, 4881692334132, 4767494130480, 1968165075084, 293636906104, 9244474934, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_41 : availableMass (start .empty) ⟨105,51,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,51,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4837826931897, 1995116067649, 215296547617, 2215688434] (by decide +kernel) (by decide +kernel)

private theorem m0_42 : availableMass (start .empty) ⟨119,40,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨119,40,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4766960833408, 1957123180374, 283102597382, 6746860711, 0] (by decide +kernel) (by decide +kernel)

private theorem m0_43 : availableMass (start .empty) ⟨111,50,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨111,50,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4837767165282, 1993968508070, 216439147462, 2469718905] (by decide +kernel) (by decide +kernel)

private theorem m0_44 : availableMass (start .empty) ⟨116,49,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,49,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4837820217381, 1996638330965, 218541394301, 2675942625] (by decide +kernel) (by decide +kernel)

private theorem m0_45 : availableMass (start .empty) ⟨122,48,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,48,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4837756820253, 1993957350216, 216999833352, 2567469958] (by decide +kernel) (by decide +kernel)

private theorem m1_0 : availableMass (start .one3) ⟨2,5,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,5,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4510228549262, 3758652508926, 3094570137710, 2512837469918, 2008253916750, 1575562266302, 1209448683566, 904542710430, 655417265678, 456588644990, 302516520942, 187603943006, 106197337550, 52586507838, 21004634030, 5628273182, 577359246, 695593] (by decide +kernel) (by decide +kernel)

private theorem m1_1 : availableMass (start .one3) ⟨2,6,0⟩ 9 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 9 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 192 [4715085774326, 3994164254364, 3225714093312, 2561046876132, 1993174140552, 1514971375404, 1119178020624, 798397467252, 545097057432, 351608084412, 210125792544, 112709377284, 51281985192, 17630713932, 3406612272, 125643554] (by decide +kernel) (by decide +kernel)

private theorem m1_2 : availableMass (start .one3) ⟨3,9,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 22 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 159 [4740005313959, 4421843870406, 3589324353974, 2659303637318, 1903252292822, 1304278111334, 845058902006, 507842492294, 274446727958, 126259473062, 44238609974, 8912039366, 378557059, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_3 : availableMass (start .one3) ⟨5,15,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .one3) ⟨5,15,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 128 [4740005313959, 4439709210263, 4152103344383, 3308726266833, 2055552124917, 1163648789049, 574493398941, 227386311969, 59451103173, 5634565257, 2899205] (by decide +kernel) (by decide +kernel)

private theorem m1_4 : availableMass (start .one3) ⟨7,20,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one3) ⟨7,20,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4740005313959, 4439709210263, 4152103344383, 3805548167150, 2440830756251, 1211944005563, 483985812651, 128719366187, 12777858299, 10811172] (by decide +kernel) (by decide +kernel)

private theorem m1_5 : availableMass (start .one3) ⟨8,24,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one3) ⟨8,24,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 107 [4740005313959, 4439709210263, 4152103344383, 3834081753949, 2376380372493, 1019014307877, 311201957397, 44561762013, 465830232] (by decide +kernel) (by decide +kernel)

private theorem m1_6 : availableMass (start .one3) ⟨64,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,4,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 236 [4089330068310, 2601240023634, 1451351205622, 591528166879, 71515649656, 7143640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_7 : availableMass (start .one3) ⟨64,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,5,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 209 [4269184843165, 2719560211224, 1527380841112, 663894111164, 114660118866, 188788480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_8 : availableMass (start .one3) ⟨65,15,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one3) ⟨65,15,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4740005313959, 4439709210263, 4152103344383, 3833502481909, 2384074719507, 1075468725903, 390943535979, 93893323431, 5882196175, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_9 : availableMass (start .one3) ⟨68,28,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨68,28,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 106 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3084237921425, 1108262844132, 243894373200, 21917824996, 83386082] (by decide +kernel) (by decide +kernel)

private theorem m1_10 : availableMass (start .one3) ⟨67,33,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,33,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 93 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2127591625884, 510657519516, 54347628444, 370154766] (by decide +kernel) (by decide +kernel)

private theorem m1_11 : availableMass (start .one3) ⟨69,34,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,34,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3154530120290, 1018179271948, 159058190456, 5036378174, 0] (by decide +kernel) (by decide +kernel)

private theorem m1_12 : availableMass (start .one3) ⟨69,37,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,37,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 96 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3259661180210, 1051979707240, 142745830440, 2606393530] (by decide +kernel) (by decide +kernel)

private theorem m1_13 : availableMass (start .one3) ⟨97,46,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨97,46,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 89 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3313891644737, 869532300029, 54062576877, 8197613] (by decide +kernel) (by decide +kernel)

private theorem m2_0 : availableMass (start .one4) ⟨2,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,4,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 207 [4493720335568, 3730708851152, 3059893912272, 2475203870672, 1970595389648, 1540053444048, 1177591320272, 877250616272, 633101241552, 439241417168, 289797675728, 178924861392, 100806129872, 49652948432, 19705095888, 5230662608, 526050512, 542036] (by decide +kernel) (by decide +kernel)

private theorem m2_1 : availableMass (start .one4) ⟨2,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,5,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 186 [4524229271836, 3684712069209, 2947617937929, 2315891461737, 1781459146425, 1336232381241, 972107438889, 680965475529, 454672530777, 285079527705, 164022272841, 83321456169, 34782651129, 10196314617, 1337786985, 9248562] (by decide +kernel) (by decide +kernel)

private theorem m2_2 : availableMass (start .one4) ⟨2,6,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 185 [4679106249028, 4236186484587, 3446219975825, 2675084564133, 2027740068761, 1493664870509, 1062240582177, 722752048565, 464387346473, 276237784701, 147297904049, 66465477317, 22541509305, 4230236813, 141283795, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_3 : availableMass (start .one4) ⟨3,9,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 22 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4679106249028, 4257353715307, 3357618985173, 2399431450645, 1642057451637, 1062655121205, 638033322133, 344651646933, 158620417845, 55700686837, 11304235605, 494411294, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_4 : availableMass (start .one4) ⟨4,12,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one4) ⟨4,12,0⟩ 40 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 143 [4679106249028, 4274622143268, 3894297784836, 3299947957636, 2199917845972, 1350093291124, 752181848852, 363009287092, 138495404116, 33654028532, 2593019284, 13496] (by decide +kernel) (by decide +kernel)

private theorem m2_5 : availableMass (start .one4) ⟨5,15,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one4) ⟨5,15,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 129 [4679106249028, 4274622143268, 3894297784836, 3413342370635, 2212572854843, 1229982837635, 591122900235, 223659386003, 53314852571, 3868071843, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_6 : availableMass (start .one4) ⟨6,17,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,17,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 124 [4679106249028, 4274622143268, 3894297784836, 3508834267095, 2361619131669, 1244641396077, 549878328045, 178748350101, 30173415525, 667461054, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_7 : availableMass (start .one4) ⟨9,27,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one4) ⟨9,27,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 109 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3066736820246, 1511632536786, 461175521230, 65904438402, 683101871, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_8 : availableMass (start .one4) ⟨67,26,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,26,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2747387744266, 977829149270, 212285627030, 18523212950, 62006450] (by decide +kernel) (by decide +kernel)

private theorem m2_9 : availableMass (start .one4) ⟨67,38,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,38,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 98 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3179501956929, 1380844791800, 200566931264, 4481952424, 0] (by decide +kernel) (by decide +kernel)

private theorem m2_10 : availableMass (start .one4) ⟨67,39,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,39,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1712697206977, 271091432801, 8119070158, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_0 : availableMass (start .one5) ⟨1,3,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 2 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4515846379624, 3765589517052, 3100699328604, 2518202934460, 2012900999196, 1579537564284, 1212800048092, 907319245884, 657669329820, 458367848956, 303875729244, 188597273532, 106880161564, 53015449980, 21237572316, 5724339004, 596937372, 834602] (by decide +kernel) (by decide +kernel)

private theorem m3_1 : availableMass (start .one5) ⟨2,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,5,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 168 [4474714919506, 3560556589897, 2771264738837, 2107386352897, 1558384260877, 1113624523577, 762376433797, 493812516337, 297008527997, 160943457577, 74499525877, 26462185697, 5520121837, 265388601] (by decide +kernel) (by decide +kernel)

private theorem m3_2 : availableMass (start .one5) ⟨2,6,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4628005587678, 4114962180234, 3291120569206, 2479051551722, 1811473134910, 1274873285554, 855509973638, 539411172346, 312374858062, 159969010370, 67531612054, 20170649098, 2764110686, 23835501, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_3 : availableMass (start .one5) ⟨3,9,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 40 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4628005587678, 4137434455250, 3682501885502, 3091820764750, 2152982527826, 1405880311010, 854008413618, 468810469826, 221085251858, 80986669986, 18023772530, 1060745858, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_4 : availableMass (start .one5) ⟨5,15,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 127 [4628005587678, 4137434455250, 3682501885502, 3214703823174, 2102202512098, 1115748186658, 497963639138, 164692735138, 28903948258, 741286152, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_5 : availableMass (start .one5) ⟨7,19,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one5) ⟨7,19,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4628005587678, 4137434455250, 3682501885502, 3231868816081, 2013813669650, 912729187778, 310718622578, 58426040354, 1940973297, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_6 : availableMass (start .one5) ⟨8,24,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one5) ⟨8,24,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2862780602178, 1669495265644, 580671791264, 114040024108, 4370303396, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_7 : availableMass (start .one5) ⟨13,39,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one5) ⟨13,39,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 103 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2190397611232, 573260101852, 35851089420, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_8 : availableMass (start .one5) ⟨67,37,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one5) ⟨67,37,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 100 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1497813043256, 225703492496, 5659896957, 0] (by decide +kernel) (by decide +kernel)

private theorem m3_9 : availableMass (start .one5) ⟨69,38,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,38,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 106 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2334508655035, 656421196795, 48975216811, 15224126] (by decide +kernel) (by decide +kernel)

private theorem m4_0 : availableMass (start .one6) ⟨1,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 204 [4577344072499, 3992070205709, 3285692264229, 2612641512381, 2036972810301, 1551572984229, 1149192811509, 822447020589, 563814291021, 365637253461, 220122489669, 119340532509, 55225865949, 19576925061, 4056096021, 189858164, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_1 : availableMass (start .one6) ⟨2,6,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one6) ⟨2,6,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 185 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2356295261492, 1661150503604, 1116637475636, 705272743604, 409142891828, 209904522932, 88784257844, 26578735796, 3654614324, 31891402, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_2 : availableMass (start .one6) ⟨6,18,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one6) ⟨6,18,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2031373053287, 999578894288, 353206261904, 72031471952, 3150045184, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m4_3 : availableMass (start .one6) ⟨11,33,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .one6) ⟨11,33,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 118 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1455144229173, 322611890582, 15222505449, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_0 : availableMass (start .one7) ⟨1,3,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 185 [4518321774336, 3832102945425, 3048257003135, 2339452199523, 1749338033831, 1267330678859, 882749539407, 584817252275, 362659686263, 205305942171, 101688352799, 40642482947, 10907129415, 1124321003, 1426177, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_1 : availableMass (start .one7) ⟨2,6,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .one7) ⟨2,6,0⟩ 39 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 165 [4518321774336, 3849816668780, 3250457160752, 2591047746536, 1799189482989, 1181112711981, 723107350861, 401727610509, 193178431533, 73315484269, 17645168781, 1324614861, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_2 : availableMass (start .one7) ⟨4,12,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .one7) ⟨4,12,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 158 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1195916871917, 570626343109, 213199551205, 49464477389, 3305317117, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m5_3 : availableMass (start .one7) ⟨8,24,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .one7) ⟨8,24,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1142533786566, 458949554126, 65589650562, 679869215, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_0 : availableMass (start .two6thin) ⟨1,3,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨1,3,0⟩ 8 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 191 [4557299675314, 3769898454084, 3030970057392, 2393897011932, 1851653064072, 1397075911284, 1022867202144, 721592536332, 485681464632, 307427488932, 178988062224, 92384588604, 39502423272, 12090872532, 1763193792, 20696658] (by decide +kernel) (by decide +kernel)

private theorem m6_1 : availableMass (start .two6thin) ⟨2,6,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨2,6,0⟩ 34 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 171 [4577344072499, 4003054728023, 3468030364838, 2694465571772, 1931499780284, 1326323578556, 861632691644, 519692862908, 282339854012, 130979444924, 46587433916, 9709637564, 462178354, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_2 : availableMass (start .two6thin) ⟨4,12,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨4,12,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2561986208349, 1760656387161, 963196679829, 451005714417, 162748953453, 34915077129, 1816270907, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_3 : availableMass (start .two6thin) ⟨6,18,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨6,18,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 129 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 1731967916972, 749396939468, 233158833644, 35073148172, 465928306, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_4 : availableMass (start .two6thin) ⟨7,19,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨7,19,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2103099927098, 1079132196286, 373919011634, 73096448182, 2776818949, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_5 : availableMass (start .two6thin) ⟨7,21,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨7,21,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 133 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1300404561693, 443754434517, 83359469157, 2726163884, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_6 : availableMass (start .two6thin) ⟨65,17,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨65,17,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 141 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2148987158629, 1089972170145, 336724907593, 64639052457, 4254497601, 3212683, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_7 : availableMass (start .two6thin) ⟨66,30,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨66,30,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 118 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1133964938058, 190819717818, 7135909117, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_8 : availableMass (start .two6thin) ⟨68,35,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨68,35,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1178570352456, 158274209944, 2372834968, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_9 : availableMass (start .two6thin) ⟨67,39,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨67,39,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1450337521229, 223414619718, 3417285910, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_10 : availableMass (start .two6thin) ⟨96,36,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨96,36,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 116 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1448240612375, 228185682197, 5176964418, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_11 : availableMass (start .two6thin) ⟨96,43,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨96,43,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 112 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1588707002848, 251288165411, 2848450083, 0] (by decide +kernel) (by decide +kernel)

private theorem m6_12 : availableMass (start .two6thin) ⟨110,42,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨110,42,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1586393220791, 248261777732, 3063673823, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_0 : availableMass (start .two6wide) ⟨1,3,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨1,3,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 230 [4487981692249, 3778312455973, 3156060990097, 2612482256909, 2041588679016, 1514937663156, 1095228971544, 767411565204, 517507679784, 332612825556, 200895787416, 111598624884, 55036672104, 22598537844, 6746105496, 1014533076, 17093028, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_1 : availableMass (start .two6wide) ⟨3,9,0⟩ 87 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨3,9,0⟩ 87 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 197 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1016312627358, 570106080178, 281149462798, 114731989018, 33507474838, 4678696258, 53703224, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_2 : availableMass (start .two6wide) ⟨5,14,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨5,14,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 181 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 750377602535, 320471801040, 99356733888, 16004503216, 338958955, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_3 : availableMass (start .two6wide) ⟨63,33,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,33,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 308402238772, 17777162800, 651180, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_4 : availableMass (start .two6wide) ⟨63,36,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,36,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 341965225228, 17227624108, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_5 : availableMass (start .two6wide) ⟨62,39,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨62,39,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 667399388575, 68442328242, 153886382, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_6 : availableMass (start .two6wide) ⟨89,40,0⟩ 110 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨89,40,0⟩ 110 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 359837600563, 12465241734, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_7 : availableMass (start .two6wide) ⟨89,45,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨89,45,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 143 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 392335955419, 11595748266, 0] (by decide +kernel) (by decide +kernel)

private theorem m7_8 : availableMass (start .two6wide) ⟨101,42,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨101,42,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 396016498519, 13357025286, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_0 : availableMass (start .two7) ⟨1,3,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .two7) ⟨1,3,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 212 [4518321774336, 3849816668780, 3250457160752, 2715142920220, 2131637545193, 1578742105301, 1130317237089, 775669558157, 504008918105, 304448398533, 166004313041, 77596207229, 28046858697, 6082277045, 331717249, 0, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_1 : availableMass (start .two7) ⟨4,11,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .two7) ⟨4,11,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 1903413969060, 1058625577860, 509622691236, 193627981572, 46654797732, 3507165060, 3358, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_2 : availableMass (start .two7) ⟨4,12,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two7) ⟨4,12,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 166 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1434154168395, 796228788773, 335419280261, 99535490733, 13359899165, 102324141, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_3 : availableMass (start .two7) ⟨7,19,0⟩ 93 < layerNeed := by
  rw [mass_eq (start .two7) ⟨7,19,0⟩ 93 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1131892846873, 493221412007, 108187249115, 6056664788, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_4 : availableMass (start .two7) ⟨8,23,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨8,23,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1154743778048, 515555506320, 87165503160, 1917706840, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_5 : availableMass (start .two7) ⟨66,32,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,32,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 430366031758, 26501188546, 13990, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_6 : availableMass (start .two7) ⟨67,34,0⟩ 97 < layerNeed := by
  rw [mass_eq (start .two7) ⟨67,34,0⟩ 97 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 478789538089, 27676522489, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_7 : availableMass (start .two7) ⟨66,36,0⟩ 97 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,36,0⟩ 97 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 465678852869, 22189278349, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_8 : availableMass (start .two7) ⟨67,35,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two7) ⟨67,35,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 592956838886, 43567101945, 2910567, 0] (by decide +kernel) (by decide +kernel)

private theorem m8_9 : availableMass (start .two7) ⟨95,40,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two7) ⟨95,40,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 616402986851, 33914846263, 0, 0] (by decide +kernel) (by decide +kernel)

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨by decide, m4_0⟩
    · exact ⟨by decide, m4_1⟩
    · exact ⟨by decide, m4_2⟩
    · exact ⟨by decide, m4_3⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨by decide, m5_0⟩
    · exact ⟨by decide, m5_1⟩
    · exact ⟨by decide, m5_2⟩
    · exact ⟨by decide, m5_3⟩
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
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m7_0⟩
    · exact ⟨by decide, m7_1⟩
    · exact ⟨by decide, m7_2⟩
    · exact ⟨by decide, m7_3⟩
    · exact ⟨by decide, m7_4⟩
    · exact ⟨by decide, m7_5⟩
    · exact ⟨by decide, m7_6⟩
    · exact ⟨by decide, m7_7⟩
    · exact ⟨by decide, m7_8⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
