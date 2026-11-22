import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Compact50PriceTable -- serialize candidate build

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
open P3_6_8_1 (sumBelow sumBelow_add)
open private P3_6_8_1.sumBelow_eq from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

private def check (f : ℕ → ℕ) (offset length : ℕ) : List ℕ → Bool
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

theorem mass_of_checks (f : ℕ → ℕ) (N : ℕ) (values : List ℕ)
    (h : check f 0 N values = true) (hv : values.sum < layerNeed) :
    P3_6_8_1.sumBelow f N < layerNeed := by
  have hs := check_sum f 0 N values h
  have hsum : P3_6_8_1.sumBelow f N = values.sum := by
    simpa only [Nat.zero_add, P3_6_8_1.sumBelow] using hs
  rwa [hsum]

theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 7 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 190 [4796260984443, 4063102190709, 3285692264229, 2612641512381, 2036972810301, 1551572984229, 1149192811509, 822447020589, 563814291021, 365637253461, 220122489669, 119340532509, 55225865949, 19576925061, 4056096021, 189858164] (by decide +kernel) (by decide +kernel)

theorem m0_1 : availableMass (start .empty) ⟨4,10,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,10,0⟩ 12 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 177 [4881692334132, 4362275118269, 3454678784497, 2681636560645, 2032695947513, 1497307677901, 1064825716609, 724507260437, 465512738185, 276905810653, 147653370641, 66625542949, 22595684377, 4240383725, 141622099] (by decide +kernel) (by decide +kernel)

theorem m0_2 : availableMass (start .empty) ⟨4,12,0⟩ 19 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 19 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 156 [4881692334132, 4765017534619, 3806509014044, 2838158327708, 2047242102812, 1416957709724, 930072537116, 568923991964, 315419499548, 151036503452, 56822465564, 13394866076, 941203484] (by decide +kernel) (by decide +kernel)

theorem m0_3 : availableMass (start .empty) ⟨10,8,0⟩ 6 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,8,0⟩ 6 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 212 [4756864958840, 3976173517668, 3205633776452, 2549479100708, 1996365331716, 1535486230244, 1156573476548, 849896670372, 606263330948, 417018896996, 274046726724, 169768097828, 97142207492, 49666172388, 21375028676, 6841732004, 1177157508, 31486558] (by decide +kernel) (by decide +kernel)

theorem m0_4 : availableMass (start .empty) ⟨11,7,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨11,7,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 236 [4515035343037, 3736804715014, 3060712102274, 2479371591790, 1983689043850, 1565013661334, 1215137989714, 926297917054, 691172674010, 502884833830, 355000312354, 241528368014, 156921601834, 96075957430, 54330721010, 27468521374, 11715329914, 3740460614, 656570050, 20021810] (by decide +kernel) (by decide +kernel)

theorem m0_5 : availableMass (start .empty) ⟨5,15,0⟩ 26 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 26 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 136 [4881692334132, 4881692334132, 4339669920712, 3057595743083, 2043613742243, 1280294832803, 733867846763, 369511856123, 151356172883, 42480349043, 4914176603, 15145481] (by decide +kernel) (by decide +kernel)

theorem m0_6 : availableMass (start .empty) ⟨6,18,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .empty) ⟨6,18,0⟩ 30 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 121 [4881692334132, 4881692334132, 4632265114002, 3208843596069, 1982603373057, 1113640202493, 543280058649, 210672133461, 52788836529, 4425795117, 353064] (by decide +kernel) (by decide +kernel)

theorem m0_7 : availableMass (start .empty) ⟨18,6,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,6,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 277 [4566984148934, 3767323230229, 3069134122153, 2472305759005, 1966566293617, 1542190313893, 1189998842809, 901359338413, 668185693825, 482938237237, 338623731913, 228795376189, 147552803473, 89542082245, 49955716057, 24532643533, 9558767068, 2015546530, 38939808, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_8 : availableMass (start .empty) ⟨8,24,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨8,24,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 104 [4881692334132, 4881692334132, 4881692334132, 3699007886408, 1979699715464, 893753145032, 301157376008, 55021902152, 1630544496] (by decide +kernel) (by decide +kernel)

theorem m0_9 : availableMass (start .empty) ⟨33,5,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,5,0⟩ 15 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 345 [4881692334132, 4573509293719, 3634087749280, 2806745548828, 2107440867296, 1523383279084, 1042419126592, 653031520220, 344505513169, 116828568242, 10703554193, 11601161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_10 : availableMass (start .empty) ⟨33,6,0⟩ 17 < layerNeed := by
  rw [mass_eq (start .empty) ⟨33,6,0⟩ 17 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 292 [4881692334132, 4673654490223, 3699012357088, 2805192124720, 2067861239872, 1468764640528, 990731176864, 617673611248, 334590924495, 129909255349, 18058545268, 85136106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_11 : availableMass (start .empty) ⟨34,9,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,9,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 206 [4881692334132, 4873511602989, 4045445684313, 2888719819881, 1993801266393, 1318677368937, 824948326617, 477827192553, 246139873881, 102325529791, 23690275878, 508438598, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_12 : availableMass (start .empty) ⟨13,39,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨13,39,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 85 [4881692334132, 4881692334132, 4881692334132, 4501740784363, 2001104563424, 493624585004, 38785923896, 353064] (by decide +kernel) (by decide +kernel)

theorem m0_13 : availableMass (start .empty) ⟨64,4,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,4,0⟩ 30 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 442 [4881692334132, 4881692334132, 4674080420284, 3416067702292, 2182526095828, 1134788463803, 299514073329, 5203022496, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_14 : availableMass (start .empty) ⟨64,5,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,5,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 361 [4881692334132, 4881692334132, 4724997171724, 3462060228478, 2191677566922, 1151080095406, 337948235545, 9239875887, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_15 : availableMass (start .empty) ⟨64,6,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,6,0⟩ 32 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 307 [4881692334132, 4881692334132, 4771827811635, 3518000766873, 2203817320341, 1163532859569, 372818575007, 15293551540, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_16 : availableMass (start .empty) ⟨65,7,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,7,0⟩ 33 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 268 [4881692334132, 4881692334132, 4812097342261, 3572255188888, 2195515974636, 1141520526624, 369415445306, 16378689889, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_17 : availableMass (start .empty) ⟨65,9,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,9,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 217 [4881692334132, 4881692334132, 4843827486638, 3601360129524, 2139502526952, 1087899257004, 371703125912, 24404435692, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_18 : availableMass (start .empty) ⟨65,10,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,10,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 199 [4881692334132, 4881692334132, 4841879353496, 3551213648396, 2063047324916, 1025398025436, 346504063602, 23740382446, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_19 : availableMass (start .empty) ⟨65,12,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨65,12,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 172 [4881692334132, 4881692334132, 4867694174592, 3608811669402, 2021004925722, 973083187098, 335051008309, 31317662841, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_20 : availableMass (start .empty) ⟨66,16,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,16,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 140 [4881692334132, 4881692334132, 4881692334132, 3791567113087, 1956503454428, 860068415164, 278905269916, 33938504423, 367290, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_21 : availableMass (start .empty) ⟨66,18,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,18,0⟩ 38 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 129 [4881692334132, 4881692334132, 4881692334132, 3907775745861, 1951687148013, 819755047449, 255622664421, 35006915664, 9150680, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_22 : availableMass (start .empty) ⟨67,20,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,20,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 121 [4881692334132, 4881692334132, 4881692334132, 4024992477256, 1947886950500, 771914990644, 222974959108, 29106787027, 11954545, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_23 : availableMass (start .empty) ⟨66,22,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,22,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 115 [4881692334132, 4881692334132, 4881692334132, 4154010769432, 1982582919107, 753579791623, 207739593643, 28757989804, 189649402, 0] (by decide +kernel) (by decide +kernel)

theorem m0_24 : availableMass (start .empty) ⟨66,24,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,24,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 109 [4881692334132, 4881692334132, 4881692334132, 4278735166543, 2020208675704, 728612670904, 185458850296, 23138742328, 266489640, 0] (by decide +kernel) (by decide +kernel)

theorem m0_25 : availableMass (start .empty) ⟨67,28,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,28,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 100 [4881692334132, 4881692334132, 4881692334132, 4375547712856, 1966618536664, 616950112616, 122270123512, 8831278216, 16115654] (by decide +kernel) (by decide +kernel)

theorem m0_26 : availableMass (start .empty) ⟨68,27,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,27,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 103 [4881692334132, 4881692334132, 4881692334132, 4384932073482, 2006230315236, 650270832648, 137041656396, 11463008496, 41510797] (by decide +kernel) (by decide +kernel)

theorem m0_27 : availableMass (start .empty) ⟨68,30,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,30,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4350628907031, 1863364542891, 533340476439, 87945494307, 3850130895, 273] (by decide +kernel) (by decide +kernel)

theorem m0_28 : availableMass (start .empty) ⟨68,33,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,33,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 93 [4881692334132, 4881692334132, 4881692334132, 4471844931148, 1903273282619, 493537267475, 65114955899, 1318411391] (by decide +kernel) (by decide +kernel)

theorem m0_29 : availableMass (start .empty) ⟨69,45,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,45,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 82 [4881692334132, 4881692334132, 4881692334132, 4774432380649, 2077002386349, 349096763229, 13001326520] (by decide +kernel) (by decide +kernel)

theorem m0_30 : availableMass (start .empty) ⟨71,43,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,43,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4676000475448, 1898478170869, 327058849413, 13712009859] (by decide +kernel) (by decide +kernel)

theorem m0_31 : availableMass (start .empty) ⟨69,49,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,49,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4767142719814, 1948447821502, 264470451418, 4356438595] (by decide +kernel) (by decide +kernel)

theorem m0_32 : availableMass (start .empty) ⟨97,28,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,28,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 101 [4881692334132, 4881692334132, 4881692334132, 4468712942135, 1879341995760, 460393442304, 41271084597, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_33 : availableMass (start .empty) ⟨98,31,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,31,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 97 [4881692334132, 4881692334132, 4881692334132, 4584396315773, 1946490016907, 442900915515, 37805032835, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m0_34 : availableMass (start .empty) ⟨84,46,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨84,46,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4767701568296, 1967869354131, 288312128863, 7858195951] (by decide +kernel) (by decide +kernel)

theorem m0_35 : availableMass (start .empty) ⟨97,36,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,36,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 90 [4881692334132, 4881692334132, 4881692334132, 4683950337693, 1983944410662, 393782679174, 27826945878, 10799059] (by decide +kernel) (by decide +kernel)

theorem m0_36 : availableMass (start .empty) ⟨97,37,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨97,37,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 89 [4881692334132, 4881692334132, 4881692334132, 4680466787974, 1949724425383, 371158753327, 23882157599, 8105669] (by decide +kernel) (by decide +kernel)

theorem m0_37 : availableMass (start .empty) ⟨98,44,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,44,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 83 [4881692334132, 4881692334132, 4881692334132, 4766722780194, 1955926011844, 287396054372, 9052704568] (by decide +kernel) (by decide +kernel)

theorem m0_38 : availableMass (start .empty) ⟨105,43,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,43,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 84 [4881692334132, 4881692334132, 4881692334132, 4766216434404, 1948074393032, 283574855044, 8880748792] (by decide +kernel) (by decide +kernel)

theorem m0_39 : availableMass (start .empty) ⟨98,52,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨98,52,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 78 [4881692334132, 4881692334132, 4881692334132, 4837998879897, 1999837077020, 214804089148, 1924648282] (by decide +kernel) (by decide +kernel)

theorem m0_40 : availableMass (start .empty) ⟨112,41,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨112,41,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 86 [4881692334132, 4881692334132, 4881692334132, 4767494130480, 1968165075084, 293636906104, 9244474934, 0] (by decide +kernel) (by decide +kernel)

theorem m0_41 : availableMass (start .empty) ⟨105,51,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨105,51,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4837826931897, 1995116067649, 215296547617, 2215688434] (by decide +kernel) (by decide +kernel)

theorem m0_42 : availableMass (start .empty) ⟨119,40,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨119,40,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 87 [4881692334132, 4881692334132, 4881692334132, 4766960833408, 1957123180374, 283102597382, 6746860711, 0] (by decide +kernel) (by decide +kernel)

theorem m0_43 : availableMass (start .empty) ⟨111,50,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨111,50,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4837767165282, 1993968508070, 216439147462, 2469718905] (by decide +kernel) (by decide +kernel)

theorem m0_44 : availableMass (start .empty) ⟨116,49,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,49,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 80 [4881692334132, 4881692334132, 4881692334132, 4837820217381, 1996638330965, 218541394301, 2675942625] (by decide +kernel) (by decide +kernel)

theorem m0_45 : availableMass (start .empty) ⟨122,48,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,48,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 81 [4881692334132, 4881692334132, 4881692334132, 4837756820253, 1993957350216, 216999833352, 2567469958] (by decide +kernel) (by decide +kernel)

theorem m0_46 : availableMass (start .empty) ⟨129,53,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨129,53,0⟩ 48 (Or.inl rfl) (by decide)]
  exact mass_of_checks _ 79 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2153477649805, 195069124125, 1125261808] (by decide +kernel) (by decide +kernel)

theorem m1_0 : availableMass (start .one3) ⟨2,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,5,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 209 [4583084299747, 3833064805960, 3160055470728, 2569940874696, 2057525884936, 1617558745416, 1244731077000, 933677877448, 678977521416, 475151760456, 316665723016, 197927914440, 113290216968, 57047889736, 23439568776, 6647267016, 796374280, 3161993] (by decide +kernel) (by decide +kernel)

theorem m1_1 : availableMass (start .one3) ⟨2,6,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 194 [4735842229374, 4086252931992, 3305845855932, 2629989821472, 2051711482884, 1563901445544, 1159314265932, 830568451632, 570146461332, 370394704824, 223523543004, 121607287872, 56584202532, 20256501192, 4290349164, 215918294, 0] (by decide +kernel) (by decide +kernel)

theorem m1_2 : availableMass (start .one3) ⟨3,9,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 27 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 164 [4740005313959, 4439709210263, 3900163686873, 2930464788614, 2121842400182, 1475622179558, 974616305174, 601206973766, 337346400374, 164556818342, 63930479318, 16129653254, 1386628406, 183475] (by decide +kernel) (by decide +kernel)

theorem m1_3 : availableMass (start .one3) ⟨5,15,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one3) ⟨5,15,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 132 [4740005313959, 4439709210263, 4152103344383, 3630894742507, 2364970094487, 1378491104619, 711234760671, 303106081779, 91833304743, 12967884027, 128366397] (by decide +kernel) (by decide +kernel)

theorem m1_4 : availableMass (start .one3) ⟨7,20,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one3) ⟨7,20,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 117 [4740005313959, 4439709210263, 4152103344383, 3840982017226, 2552715538767, 1282667460143, 522648039071, 144790374879, 16097570351, 36685823] (by decide +kernel) (by decide +kernel)

theorem m1_5 : availableMass (start .one3) ⟨8,24,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3) ⟨8,24,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2786297300517, 1257395782413, 422858453709, 76752635493, 2211709670, 0] (by decide +kernel) (by decide +kernel)

theorem m1_6 : availableMass (start .one3) ⟨64,4,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,4,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 276 [4740005313959, 4439709210263, 4152103344383, 3645923222697, 2418950198518, 1408157751890, 657874483979, 145343596691, 819965860, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_7 : availableMass (start .one3) ⟨64,5,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .one3) ⟨64,5,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 248 [4740005313959, 4439709210263, 4152103344383, 3692384424342, 2444277371658, 1404707717850, 659751558058, 163885640090, 1848657821, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_8 : availableMass (start .one3) ⟨65,15,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one3) ⟨65,15,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2649106112247, 1224797545683, 464046124239, 122083087851, 11202390336, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m1_9 : availableMass (start .one3) ⟨68,28,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨68,28,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 106 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3084237921425, 1108262844132, 243894373200, 21917824996, 83386082] (by decide +kernel) (by decide +kernel)

theorem m1_10 : availableMass (start .one3) ⟨67,33,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,33,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3166198484653, 1058107213986, 179469608082, 7333291449, 0] (by decide +kernel) (by decide +kernel)

theorem m1_11 : availableMass (start .one3) ⟨69,34,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,34,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 99 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3279316199279, 1140850577716, 190245883144, 7414842199, 0] (by decide +kernel) (by decide +kernel)

theorem m1_12 : availableMass (start .one3) ⟨69,37,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,37,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 96 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3259661180210, 1051979707240, 142745830440, 2606393530] (by decide +kernel) (by decide +kernel)

theorem m1_13 : availableMass (start .one3) ⟨97,46,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3) ⟨97,46,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 90 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3428922326525, 1018600936677, 72694276629, 50640980] (by decide +kernel) (by decide +kernel)

theorem m2_0 : availableMass (start .one4) ⟨2,4,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,4,0⟩ 5 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 211 [4600464214238, 3851310507872, 3165551884896, 2566928134496, 2049391201376, 1606921341792, 1233527123552, 923245426016, 670141440096, 468308668256, 311868924512, 194972334432, 111797335136, 56550675296, 23467415136, 6810926432, 872892512, 5322424] (by decide +kernel) (by decide +kernel)

theorem m2_1 : availableMass (start .one4) ⟨2,5,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,5,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 198 [4679106249028, 4128943668588, 3340854006297, 2652150741513, 2065145046441, 1571763426873, 1163917272057, 833502854697, 572401330953, 372478740441, 225586006233, 123558934857, 58218216297, 21369423993, 4803014841, 294329193, 0] (by decide +kernel) (by decide +kernel)

theorem m2_2 : availableMass (start .one4) ⟨2,6,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 22 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4679106249028, 4263074300183, 3529677448163, 2745781921575, 2086692805067, 1541900921039, 1100800323891, 752688300023, 486765367835, 292135277727, 157805012099, 72684785351, 25588043883, 5231466095, 235246722, 0] (by decide +kernel) (by decide +kernel)

theorem m2_3 : availableMass (start .one4) ⟨3,9,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 36 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 162 [4679106249028, 4274622143268, 3894297784836, 3150447984283, 2234469051459, 1514539017291, 967797908851, 571036482939, 300696226083, 132869354539, 43298814291, 7378281051, 170601674, 0] (by decide +kernel) (by decide +kernel)

theorem m2_4 : availableMass (start .one4) ⟨4,12,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one4) ⟨4,12,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 147 [4679106249028, 4274622143268, 3894297784836, 3470510246596, 2455203628772, 1536328812548, 879854327076, 442860744260, 181522666340, 51108725892, 5981585828, 20166814, 0] (by decide +kernel) (by decide +kernel)

theorem m2_5 : availableMass (start .one4) ⟨5,15,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one4) ⟨5,15,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2620807791973, 1510572121165, 767131933565, 318855356533, 92166731701, 11546614973, 59772489, 0] (by decide +kernel) (by decide +kernel)

theorem m2_6 : availableMass (start .one4) ⟨6,17,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,17,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 129 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2819114545598, 1568231280840, 742552020516, 273772896960, 61734131292, 3779475384, 0] (by decide +kernel) (by decide +kernel)

theorem m2_7 : availableMass (start .one4) ⟨9,27,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one4) ⟨9,27,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 110 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3120414221150, 1621537499610, 511450047910, 79492178754, 1220336594, 0] (by decide +kernel) (by decide +kernel)

theorem m2_8 : availableMass (start .one4) ⟨67,26,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,26,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3185195628133, 1665520157918, 450415773182, 65139367646, 1796077865, 0] (by decide +kernel) (by decide +kernel)

theorem m2_9 : availableMass (start .one4) ⟨67,38,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,38,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 101 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1903017223139, 341707469516, 14931680852, 0] (by decide +kernel) (by decide +kernel)

theorem m2_10 : availableMass (start .one4) ⟨67,39,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,39,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 100 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1887403815926, 323307057216, 12040142596, 0] (by decide +kernel) (by decide +kernel)

theorem m3_0 : availableMass (start .one5) ⟨1,3,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 5 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 211 [4571052057750, 3831891889980, 3159090854172, 2569158301180, 2056900867548, 1617068566716, 1244354789020, 933396301692, 678773248860, 475009151548, 316570907676, 197868792060, 113256456412, 57030929340, 23432616348, 6645299836, 796139100, 3161061] (by decide +kernel) (by decide +kernel)

theorem m3_1 : availableMass (start .one5) ⟨2,5,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,5,0⟩ 28 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 193 [4628005587678, 4137434455250, 3577368564255, 2801575284099, 2132681043847, 1579104078315, 1130214480303, 775285574611, 503493918039, 303919299387, 165544739455, 77256491043, 27844038951, 6000099979, 320646401, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m3_2 : availableMass (start .one5) ⟨2,6,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 34 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 184 [4628005587678, 4137434455250, 3672106318213, 2938469058790, 2187676090818, 1575770253822, 1089156297562, 714008974998, 436273042290, 241663258798, 115664387082, 43531192902, 10288445218, 730916190, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m3_3 : availableMass (start .one5) ⟨3,9,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 163 [4628005587678, 4137434455250, 3682501885502, 3247589219638, 2438233606346, 1622742945674, 1011442002762, 575993881610, 287416824266, 116084210826, 31724559434, 3421526282, 6282380, 0] (by decide +kernel) (by decide +kernel)

theorem m3_4 : availableMass (start .one5) ⟨5,15,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 139 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2831040273752, 1814878336168, 929137435928, 390972502408, 115591497208, 15326989928, 109171667, 0] (by decide +kernel) (by decide +kernel)

theorem m3_5 : availableMass (start .one5) ⟨7,19,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one5) ⟨7,19,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 129 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1998132144164, 903629040740, 306378901412, 57067596260, 1831909965, 0] (by decide +kernel) (by decide +kernel)

theorem m3_6 : availableMass (start .one5) ⟨8,24,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .one5) ⟨8,24,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2161595634390, 872445757864, 220826126628, 18925059576, 2191005] (by decide +kernel) (by decide +kernel)

theorem m3_7 : availableMass (start .one5) ⟨13,39,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨13,39,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 105 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2356831775938, 748870310470, 63286097670, 5005851] (by decide +kernel) (by decide +kernel)

theorem m3_8 : availableMass (start .one5) ⟨67,37,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .one5) ⟨67,37,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 108 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2408384426622, 777730151302, 72272921902, 165099146] (by decide +kernel) (by decide +kernel)

theorem m3_9 : availableMass (start .one5) ⟨69,38,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,38,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 107 [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 2405616089379, 754795856760, 63645847428, 70177583] (by decide +kernel) (by decide +kernel)

theorem m4_0 : availableMass (start .one6) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4577344072499, 4003054728023, 3366791307861, 2682487153221, 2096347002909, 1601272799709, 1190030437509, 855249761301, 589424567181, 384912602349, 233935565109, 128579104869, 60792822141, 22390268541, 5048946789, 310310709, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m4_1 : availableMass (start .one6) ⟨2,6,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one6) ⟨2,6,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2418557094552, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m4_2 : availableMass (start .one6) ⟨6,18,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .one6) ⟨6,18,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1366145661992, 544805823848, 144231497384, 14092322792, 9979604, 0] (by decide +kernel) (by decide +kernel)

theorem m4_3 : availableMass (start .one6) ⟨11,33,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .one6) ⟨11,33,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 120 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1604130494819, 424280859137, 28102404257, 0] (by decide +kernel) (by decide +kernel)

theorem m5_0 : availableMass (start .one7) ⟨1,3,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 227 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1770426457521, 1285734251565, 897536311361, 596302315637, 371192001993, 211268340029, 105497531345, 42749009541, 11795440217, 1312720973, 3128777, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_1 : availableMass (start .one7) ⟨2,6,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .one7) ⟨2,6,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 206 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1451831965581, 965445253227, 569653126035, 299970277723, 132549667203, 43194983115, 7360643827, 170195010, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_2 : availableMass (start .one7) ⟨4,12,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .one7) ⟨4,12,0⟩ 91 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1114971031949, 569243768741, 212686092165, 49346039597, 3297444125, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m5_3 : availableMass (start .one7) ⟨8,24,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .one7) ⟨8,24,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 690060869944, 140651663122, 5579161980, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_0 : availableMass (start .two6a) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨1,3,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4577344072499, 4003054728023, 3366791307861, 2682487153221, 2096347002909, 1601272799709, 1190030437509, 855249761301, 589424567181, 384912602349, 233935565109, 128579104869, 60792822141, 22390268541, 5048946789, 310310709, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_1 : availableMass (start .two6a) ⟨2,6,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨2,6,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 187 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2418557094552, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_2 : availableMass (start .two6a) ⟨4,12,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨4,12,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2045321582483, 1194353895009, 593780802141, 237828624249, 63711635637, 6467328273, 6858633, 0] (by decide +kernel) (by decide +kernel)

theorem m6_3 : availableMass (start .two6a) ⟨6,18,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨6,18,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1366145661992, 544805823848, 144231497384, 14092322792, 9979604, 0] (by decide +kernel) (by decide +kernel)

theorem m6_4 : availableMass (start .two6a) ⟨7,19,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨7,19,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 138 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1342362919938, 507693938534, 120547499930, 8597724126, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_5 : availableMass (start .two6a) ⟨7,21,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨7,21,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 134 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1377995462403, 481969888683, 95854492419, 3835559999, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_6 : availableMass (start .two6a) ⟨65,17,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨65,17,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 145 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1409393068617, 476900458633, 107279828497, 10395721553, 70417740, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m6_7 : availableMass (start .two6a) ⟨66,30,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨66,30,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 123 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1586333634799, 396791634948, 30996851460, 17749878, 0] (by decide +kernel) (by decide +kernel)

theorem m6_8 : availableMass (start .two6a) ⟨68,35,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨68,35,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 119 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1631325671486, 374112313957, 17701607866, 0] (by decide +kernel) (by decide +kernel)

theorem m6_9 : availableMass (start .two6a) ⟨67,39,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨67,39,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 115 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1616157859765, 322690207749, 8627959064, 0] (by decide +kernel) (by decide +kernel)

theorem m6_10 : availableMass (start .two6a) ⟨96,36,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨96,36,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 118 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1614705776891, 326361170993, 11367635411, 0] (by decide +kernel) (by decide +kernel)

theorem m6_11 : availableMass (start .two6a) ⟨96,43,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨96,43,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 113 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1664095392885, 308215185229, 4873067974, 0] (by decide +kernel) (by decide +kernel)

theorem m6_12 : availableMass (start .two6a) ⟨110,42,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6a) ⟨110,42,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 114 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1662417998766, 304743991040, 5124444800, 0] (by decide +kernel) (by decide +kernel)

theorem m7_0 : availableMass (start .two6b) ⟨1,3,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨1,3,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 224 [4532662882374, 3890683591998, 3317021852982, 2767448438224, 2152552626381, 1629711544989, 1202856807549, 860872295469, 593110503021, 389392537341, 240008118429, 135715579149, 67741865229, 27782535261, 8001760701, 1032325869, 7028093, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_1 : availableMass (start .two6b) ⟨2,6,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨2,6,0⟩ 63 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 200 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1861897069134, 1271151892036, 820139724244, 493491909988, 269494622452, 127437325444, 47612773396, 11317011364, 849375028, 2618, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_2 : availableMass (start .two6b) ⟨4,12,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨4,12,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 169 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1535695693038, 865118316504, 401637872136, 144922610424, 31825688232, 1860774168, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_3 : availableMass (start .two6b) ⟨6,18,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨6,18,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 963822337788, 349218510492, 77094129468, 4550949084, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_4 : availableMass (start .two6b) ⟨7,19,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨7,19,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 150 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 945977811831, 323268673783, 62773759935, 2441625345, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_5 : availableMass (start .two6b) ⟨7,21,0⟩ 85 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨7,21,0⟩ 85 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 146 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 973259349900, 305661548544, 48305454828, 844958010, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_6 : availableMass (start .two6b) ⟨65,17,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨65,17,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 990664969191, 291211257831, 49975378551, 2471613655, 25790, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_7 : availableMass (start .two6b) ⟨66,30,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨66,30,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 135 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1128634434036, 244182446652, 13009372428, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m7_8 : availableMass (start .two6b) ⟨68,35,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨68,35,0⟩ 91 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 131 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1163075302888, 230433868198, 6927171146, 0] (by decide +kernel) (by decide +kernel)

theorem m7_9 : availableMass (start .two6b) ⟨67,39,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨67,39,0⟩ 91 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 127 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1151983300332, 196943878656, 2976500244, 0] (by decide +kernel) (by decide +kernel)

theorem m7_10 : availableMass (start .two6b) ⟨96,36,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨96,36,0⟩ 91 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 130 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1149979521570, 196702478016, 3963887730, 0] (by decide +kernel) (by decide +kernel)

theorem m7_11 : availableMass (start .two6b) ⟨96,43,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨96,43,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 125 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1187827819996, 187115806402, 1479627838, 0] (by decide +kernel) (by decide +kernel)

theorem m7_12 : availableMass (start .two6b) ⟨110,42,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two6b) ⟨110,42,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 126 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1186285348460, 183764139472, 1536662120, 0] (by decide +kernel) (by decide +kernel)

theorem m8_0 : availableMass (start .two6c) ⟨1,3,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨1,3,0⟩ 71 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 254 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1739893742309, 1322204277864, 945330837204, 653606889816, 433613983476, 273006940584, 160513858164, 85936107864, 40148335956, 15098463336, 3807685524, 370472664, 462208, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_1 : availableMass (start .two6c) ⟨3,9,0⟩ 98 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨3,9,0⟩ 98 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 772204129689, 410151901939, 187610462899, 67510852459, 15323742619, 1068765379, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_2 : availableMass (start .two6c) ⟨5,14,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨5,14,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 186 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 837990242393, 415770521200, 143901155328, 29901115536, 1573007530, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_3 : availableMass (start .two6c) ⟨63,33,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨63,33,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 155 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 519822313483, 60813571246, 386041040, 0] (by decide +kernel) (by decide +kernel)

theorem m8_4 : availableMass (start .two6c) ⟨63,36,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨63,36,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 152 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 512116672915, 50677508524, 103124004, 0] (by decide +kernel) (by decide +kernel)

theorem m8_5 : availableMass (start .two6c) ⟨62,39,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨62,39,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 504993813523, 42290782650, 14522224, 0] (by decide +kernel) (by decide +kernel)

theorem m8_6 : availableMass (start .two6c) ⟨89,40,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨89,40,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 149 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 531742286476, 44066256930, 18567124, 0] (by decide +kernel) (by decide +kernel)

theorem m8_7 : availableMass (start .two6c) ⟨89,45,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨89,45,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 146 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 522754422120, 33770744594, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m8_8 : availableMass (start .two6c) ⟨101,42,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two6c) ⟨101,42,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 148 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 524922929462, 36659500662, 2504655, 0] (by decide +kernel) (by decide +kernel)

theorem m9_0 : availableMass (start .two6d) ⟨1,3,0⟩ 98 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨1,3,0⟩ 98 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 281 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 758388985164, 510289830300, 327689803488, 198506814276, 111363563784, 56197892460, 24262780080, 8126345748, 1671847896, 97684284, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_1 : availableMass (start .two6d) ⟨3,9,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨3,9,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 230 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 363911072276, 165593987696, 59893494356, 14095182656, 1153346996, 225571, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_2 : availableMass (start .two6d) ⟨5,14,0⟩ 126 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨5,14,0⟩ 126 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 208 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 408132949982, 161585526802, 39549050546, 3572663890, 2275995, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_3 : availableMass (start .two6d) ⟨63,33,0⟩ 133 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨63,33,0⟩ 133 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 175 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 154259081112, 4647135522, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_4 : availableMass (start .two6d) ⟨63,36,0⟩ 134 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨63,36,0⟩ 134 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 173 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 171746221394, 4711830976, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_5 : availableMass (start .two6d) ⟨62,39,0⟩ 134 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨62,39,0⟩ 134 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 170 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 166431902038, 3321480202, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_6 : availableMass (start .two6d) ⟨89,40,0⟩ 134 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨89,40,0⟩ 134 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 169 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 157717169123, 2042184170, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m9_7 : availableMass (start .two6d) ⟨89,45,0⟩ 135 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨89,45,0⟩ 135 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 167 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 175134650865, 1939569480, 0] (by decide +kernel) (by decide +kernel)

theorem m9_8 : availableMass (start .two6d) ⟨101,42,0⟩ 135 < layerNeed := by
  rw [mass_eq (start .two6d) ⟨101,42,0⟩ 135 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 169 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 176501525201, 2269551708, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_0 : availableMass (start .two7a) ⟨1,3,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨1,3,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 227 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1770426457521, 1285734251565, 897536311361, 596302315637, 371192001993, 211268340029, 105497531345, 42749009541, 11795440217, 1312720973, 3128777, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_1 : availableMass (start .two7a) ⟨4,11,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨4,11,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 181 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1101811002251, 568485537666, 225148525602, 59158258242, 5721868770, 3822495, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_2 : availableMass (start .two7a) ⟨4,12,0⟩ 91 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨4,12,0⟩ 91 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1114971031949, 569243768741, 212686092165, 49346039597, 3297444125, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_3 : availableMass (start .two7a) ⟨7,19,0⟩ 97 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨7,19,0⟩ 97 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 651569701633, 168397406021, 15469709353, 5467237, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_4 : availableMass (start .two7a) ⟨8,23,0⟩ 98 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨8,23,0⟩ 98 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 153 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 655277592973, 133435364508, 5636477555, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m10_5 : availableMass (start .two7a) ⟨66,32,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨66,32,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 143 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 710192408502, 88044454106, 464546250, 0] (by decide +kernel) (by decide +kernel)

theorem m10_6 : availableMass (start .two7a) ⟨67,34,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨67,34,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 141 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 702194500631, 76851869593, 170160312, 0] (by decide +kernel) (by decide +kernel)

theorem m10_7 : availableMass (start .two7a) ⟨66,36,0⟩ 102 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨66,36,0⟩ 102 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 140 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 741722072546, 85628056269, 154519259, 0] (by decide +kernel) (by decide +kernel)

theorem m10_8 : availableMass (start .two7a) ⟨67,35,0⟩ 102 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨67,35,0⟩ 102 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 141 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 744438223572, 90466664199, 255833637, 0] (by decide +kernel) (by decide +kernel)

theorem m10_9 : availableMass (start .two7a) ⟨95,40,0⟩ 102 < layerNeed := by
  rw [mass_eq (start .two7a) ⟨95,40,0⟩ 102 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 137 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 723194235215, 61251996663, 5088636, 0] (by decide +kernel) (by decide +kernel)

theorem m11_0 : availableMass (start .two7b) ⟨1,3,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨1,3,0⟩ 84 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 249 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1007519059678, 680844650494, 435119232350, 258047048446, 137733237982, 62683836158, 21805774174, 4406879230, 196109227, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_1 : availableMass (start .two7b) ⟨4,11,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨4,11,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 199 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 475651310037, 181741680033, 44889927693, 3714486297, 292680, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_2 : availableMass (start .two7b) ⟨4,12,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨4,12,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 195 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 486863050806, 176795236706, 39078366686, 2300772330, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_3 : availableMass (start .two7b) ⟨7,19,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨7,19,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 177 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 547590139677, 158152630178, 15267359546, 10811342, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_4 : availableMass (start .two7b) ⟨8,23,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨8,23,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 170 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 556178909940, 140639433603, 7397417533, 0, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_5 : availableMass (start .two7b) ⟨66,32,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨66,32,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 160 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 590639824548, 128989160029, 1715353640, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_6 : availableMass (start .two7b) ⟨67,34,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨67,34,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 158 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 589814778492, 120413491120, 1020712048, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_7 : availableMass (start .two7b) ⟨66,36,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨66,36,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 156 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 589069042311, 112951246142, 578738935, 0] (by decide +kernel) (by decide +kernel)

theorem m11_8 : availableMass (start .two7b) ⟨67,35,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨67,35,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 157 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 589423100453, 116489020572, 772699270, 0, 0] (by decide +kernel) (by decide +kernel)

theorem m11_9 : availableMass (start .two7b) ⟨95,40,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two7b) ⟨95,40,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_checks _ 154 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 599990712433, 118687999192, 305264699, 0] (by decide +kernel) (by decide +kernel)

theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m8_0⟩
    · exact ⟨by decide, m8_1⟩
    · exact ⟨by decide, m8_2⟩
    · exact ⟨by decide, m8_3⟩
    · exact ⟨by decide, m8_4⟩
    · exact ⟨by decide, m8_5⟩
    · exact ⟨by decide, m8_6⟩
    · exact ⟨by decide, m8_7⟩
    · exact ⟨by decide, m8_8⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m9_0⟩
    · exact ⟨by decide, m9_1⟩
    · exact ⟨by decide, m9_2⟩
    · exact ⟨by decide, m9_3⟩
    · exact ⟨by decide, m9_4⟩
    · exact ⟨by decide, m9_5⟩
    · exact ⟨by decide, m9_6⟩
    · exact ⟨by decide, m9_7⟩
    · exact ⟨by decide, m9_8⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
end Final50PriceMass
