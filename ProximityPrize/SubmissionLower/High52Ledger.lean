import ProximityPrize.SubmissionLower.High52ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High52

open Finset
open High52_3
open K1_14 (Shape)

set_option maxHeartbeats 8000000

private def Fits (hi r : ℕ) (s : Shape) : Prop :=
  2 ≤ s.B ∧ 0 < s.J ∧ s.J ≤ s.B ∧ s.B < p ∧ s.U < p ∧
    0 < s.m*agreement ∧ 2*hi*r ≤ fullCutoff s

private instance (hi r : ℕ) (s : Shape) : Decidable (Fits hi r s) := by
  unfold Fits
  infer_instance

private theorem guard_of_fits {h r : ℕ} {s : Shape} (hf : Fits h r s) :
    BankGuard h r s :=
  ⟨⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.2.2.2.2.2.2⟩

private theorem checked_fits (b : Band) :
    (stages b).all (fun s => decide (Fits (finish b) s.reserve s.free.shape ∧
       Fits (finish b) s.reserve s.moving.shape)) = true := by
  cases b <;> decide +kernel

theorem schedule (b : Band) : ScheduleOK b := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · cases b <;> decide
  · cases b <;> decide
  · have H : ∀ i : Fin (laterCount b), 0 < (stageAt b (i+1)).reserve := by cases b <;> decide +kernel
    exact fun i hi => H ⟨i,hi⟩
  · have H : ∀ i : Fin (stages b).length, (stageAt b i).reserve < p := by cases b <;> decide +kernel
    exact fun i hi => H ⟨i,hi⟩
  · cases b <;> decide
  · have H : (introIndices b).all (fun i => decide (0 < i ∧ i < (stages b).length)) = true := by
      cases b <;> decide +kernel
    exact fun i hi => of_decide_eq_true (List.all_eq_true.mp H i hi)
  · cases b <;> decide +kernel
  · intro i hi
    obtain ⟨x,y⟩ := of_decide_eq_true (List.all_eq_true.mp (checked_fits b) _ (stage_mem hi))
    exact ⟨guard_of_fits x,guard_of_fits y⟩
  · apply guard_of_fits
    cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · have H : 2 ≤ rankB b ∧ 0 < rankJ b ∧ rankJ b ≤ rankB b ∧ rankB b < p := by
      cases b <;> decide +kernel
    exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2⟩
  · cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · cases b <;> decide +kernel

open HighCore82268JointRank (splice)
open High52JointRank (capB capJ lambdaDegree)

private def historyTable : List Mass := [![6436, 75687, 361194, 1912651],
  ![4451, 75687, 361194, 1912651],
  ![(35767/9), (551249/9), (2540906/9), (3498287/3)],
  ![2695, (341527/8), 275132, (6112733/8)],
  ![(53983/36), (211139/9), (3857993/25), (16672716/25)],
  ![(67168/81), (1124038/81), (5225424/49), (3384535/8)],
  ![(57277/98), (927861/98), (8455369/121), (42568367/144)],
  ![(147903/361), (2616705/361), (12162157/225), (42568367/144)],
  ![(147903/361), (2616705/361), (12162157/225), (22181030/121)],
  ![(205091/841), (2616705/361), (12162157/225), (22181030/121)],
  ![(205091/841), (5692875/961), (5233409/125), (22181030/121)],
  ![(205091/841), (5469979/1058), (50466089/1369), (22181030/121)],
  ![(600622/3249), (5469979/1058), (50466089/1369), (22181030/121)],
  ![(600622/3249), (17986888/3721), (81744181/2401), (22181030/121)],
  ![(7646967/48223), (17986888/3721), (81744181/2401), (22181030/121)],
  ![(106945/726), (17986888/3721), (81744181/2401), (22181030/121)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)],
  ![(106945/726), (44810713/10000), (67532992/2187), (101979571/588)]]

private def rankReceipt : Mass := ![6436, 75687, 361194, 1912651]

private def receipt (i : ℕ) : Mass := historyTable[i]?.getD (fun _ => 0)

private theorem receipt_zero : history .h2452 0 = receipt 0 := by
  funext k
  fin_cases k <;> decide +kernel

private theorem receipt_check :
    ∀ i : Fin (laterCount .h2452), ∀ k : Fin 4,
      capMin (receipt i) (stageCap .h2452 (i+1) (decide (stopIndex .h2452 ≤ i+1))) k =
        receipt (i+1) k := by
  intro i k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (i : ℕ) (hi : i ≤ laterCount .h2452) :
    history .h2452 i = receipt i := by
  induction i with
  | zero => exact receipt_zero
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount .h2452)]
    funext k
    exact receipt_check ⟨i,by omega⟩ k

private theorem rank_eq : rankMass .h2452 = rankReceipt := by
  funext k
  fin_cases k <;> decide +kernel

private def rate0 (i : ℕ) : ℚ := ([157279359, 144869196, 131982502, 117200667, 96373104, 75508731, 62635113, 65612009, 56999017, 58375514, 65560191, 59268360, 59944081, 72075210, 92545663, 85123592, 727772157, 961594537, 236745160, 532676609, 710235478, 532676609, 213070644, 304386634, 193700585, 142047096, 118372580, 304386634, 133169153, 133551009] : List ℚ)[i]?.getD 0
private def rate1 (i : ℕ) : ℚ := ([2446059, 2663413, 2945975, 3342046, 4108079, 5296527, 6427255, 6122718, 7083377, 6906560, 6127414, 6803780, 6725995, 5561656, 4287329, 4678144, 370103, 213625, 1557311, 583993, 389329, 583993, 1751974, 1167983, 1946638, 2725292, 3309283, 1167983, 2919956, 2911583] : List ℚ)[i]?.getD 0
private def optimum (i : ℕ) : ℕ := ([7, 8, 8, 9, 11, 14, 17, 16, 19, 18, 16, 18, 18, 15, 12, 13, 2, 1, 5, 2, 2, 2, 5, 4, 6, 8, 9, 4, 8, 8] : List ℕ)[i]?.getD 0

abbrev Q : ℚ := ((p+1 : ℕ) : ℚ)
private def alpha (hi : ℕ) : ℚ := 1 + 2 * ((blockLength : ℚ) / agreement) * degreeAt hi
private def mu (hi : ℕ) : ℚ := ((blockLength - degreeAt hi : ℕ) : ℚ) / gap hi
private def drop (a : ℚ) := a / Q
private def quad (hi : ℕ) (a : ℚ) := 2 * alpha hi * drop a
private def slope (hi : ℕ) (a : ℚ) := 2 * alpha hi - (mu hi - alpha hi) * drop a
def raw (hi : ℕ) (a : ℚ) (g : ℕ) :=
  (1 - a * g / Q) * curveUnit hi g
private theorem raw_eq (hi : ℕ) (a : ℚ) (g : ℕ) :
    raw hi a g = -(quad hi a) * (g : ℚ)^2 + slope hi a * g + (mu hi - alpha hi) := by
  unfold raw curveUnit quad slope drop mu alpha
  ring
private theorem raw_le_peak (hi : ℕ) (a : ℚ) (g m : ℕ) (hg : 0 < g)
    (hquad : 0 ≤ quad hi a)
    (hleft : m = 1 ∨ quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)
    (hright : slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) :
    raw hi a g ≤ raw hi a m := by
  rw [raw_eq, raw_eq]
  rcases lt_trichotomy g m with h | rfl | h
  · have he : 0 ≤ (m : ℚ) - g := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : (g : ℚ) + m ≤ 2 * (m : ℚ) - 1 := by
      have hh : (g : ℚ) + 1 ≤ m := by exact_mod_cast h
      linarith only [hh]
    have hb : quad hi a * ((g : ℚ) + m) ≤ slope hi a := by
      rcases hleft with hm | hm
      · omega
      · exact (mul_le_mul_of_nonneg_left hgm hquad).trans hm
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
  · exact le_rfl
  · have he : 0 ≤ (g : ℚ) - m := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : 2 * (m : ℚ) + 1 ≤ (g : ℚ) + m := by
      have hh : (m : ℚ) + 1 ≤ g := by exact_mod_cast h
      linarith only [hh]
    have hb : slope hi a ≤ quad hi a * ((g : ℚ) + m) :=
      hright.trans (mul_le_mul_of_nonneg_left hgm hquad)
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
def rateCheck (hi : ℕ) (a h : ℚ) (m : ℕ) : Bool :=
  decide (Q/81 ≤ a) && decide (0 ≤ h) && decide (0 ≤ quad hi a) &&
    (decide (m = 1) || decide (quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)) &&
    decide (slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) && decide (raw hi a m ≤ h)
theorem rate_of_check {hi : ℕ} {a h : ℚ} {m : ℕ}
    (hc : rateCheck hi a h m = true) : RateOK hi a h := by
  simp only [rateCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨ha, hh⟩, hquad⟩, hl⟩, hr⟩, hp⟩
  refine ⟨ha, hh, fun g hg _ => ?_⟩
  by_cases hz : 0 ≤ 1 - a * g / Q
  · rw [max_eq_right hz]
    exact (raw_le_peak hi a g m hg hquad hl hr).trans hp
  · rw [max_eq_left (le_of_not_ge hz), zero_mul]
    exact hh


private theorem rate_valid (i : Fin (laterCount .h2452+1)) : RateOK (finish .h2452) (rate0 i) (rate1 i) := by
  apply rate_of_check (m := optimum i)
  fin_cases i <;> decide +kernel

private def seedRegisterTable : List Mass := [![0, 0, 0, 0],
  ![12582, 445, 118, 0],
  ![13683, 489, 130, 0],
  ![15019, 521, 138, 0],
  ![17153, 612, 163, 0],
  ![20860, 717, 191, 0],
  ![26293, 942, 253, 0],
  ![32090, 1146, 305, 0],
  ![41851, 1346, 357, 0],
  ![48175, 1454, 385, 0],
  ![48175, 1662, 443, 0],
  ![65571, 2322, 628, 0],
  ![97166, 2360, 634, 0],
  ![97166, 2961, 788, 0],
  ![158016, 3099, 819, 0],
  ![208880, 3099, 819, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![208880, 4708, 1261, 0],
  ![226349, 7850, 2106, 0]]

private def lossRegisterTable : List Mass := [![0, 0, 0, 0],
  ![1978888894938, 100765629093, 18558964362, 288634962],
  ![1982245208868, 107284516923, 18832995480, 346243690],
  ![1982245208868, 113008482067, 18832995480, 406544550],
  ![2010343041051, 129052923242, 19103708721, 544753498],
  ![2010343041051, 154794043508, 19103708721, 784643089],
  ![2010343041051, 210390809013, 19103708943, 1340021331],
  ![2010343041051, 278030452448, 19103709465, 1960312775],
  ![2745928188659, 344555635132, 23423487213, 2185810326],
  ![2745928188659, 424118257693, 23423487213, 2727100145],
  ![2765831853320, 424252917068, 25860352702, 3059606080],
  ![4298847284061, 554011426896, 41171799948, 3848015992],
  ![5758869467760, 800969417080, 41171799948, 4313596520],
  ![5758869467760, 800969417080, 47235935828, 5300084060],
  ![11389036383360, 1102191710286, 59029596990, 5300084060],
  ![19330938087440, 1102191746999, 59029596990, 5300084060],
  ![19330938087440, 1102191746999, 107340849512, 5899139584],
  ![21125770173396, 1102191746999, 107340849512, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![28802641166761, 1102191746999, 135584829717, 5899139584],
  ![30229137336141, 1707409321117, 281258424954, 6131793798]]

private def seedChargeTable : List ℚ := [157279359, 12565107, 9527992, (132114397/8), (11108690969/900), (18838620578/1323), (15166869771/1694), (670888002379/81225), (20893273324/4275), (377113037266/81225), (321209603204133/20205025), (4947081965663600/609053041), (12723069964799/1448402), (376521804248667775/29026959129), (388955329488/48223), (203930290699034/8934121), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (56558502470371621/1323135000)]

private def seedCredit : ℚ := (3171416043940989773041066672679597988694157/8603355769546683433121086784107500)

open High50Nonlinear (remainder charge charge_over_range)

private def tariffWeights (mode : Bool) : ℕ → Mass :=
  if mode then lossWeight .h2452 rate0 rate1 else cutWeight .h2452 0

private def registry (mode : Bool) (i : ℕ) : Mass :=
  ((if mode then lossRegisterTable else seedRegisterTable)[i]?).getD (fun _ => 0)

private theorem register_step (mode : Bool) :
    ∀ i : Fin (laterCount .h2452+1), ∀ k : Fin 4,
      max (registry mode i k) (tariffWeights mode i k) = registry mode (i+1) k := by
  cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (mode : Bool) (i : ℕ) (hi : i ≤ laterCount .h2452+1) :
    running (tariffWeights mode) i = registry mode i := by
  induction i with
  | zero => funext k; cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount .h2452+1)]
    exact register_step mode ⟨i,by omega⟩ k

private def seedCharge (i : ℕ) : ℚ := seedChargeTable[i]?.getD 0

private theorem seed_charge_eq : ∀ i : Fin (laterCount .h2452+1),
    dotQ (fun k => registry false (i+1) k - registry false i k) (receipt i) = seedCharge i := by
  intro i
  fin_cases i <;> decide +kernel

private theorem seed_exact : seedLimit .h2452 = seedCredit := by
  unfold seedLimit weightedBill
  trans (∑ i ∈ range (laterCount .h2452+1), seedCharge i)
  · apply sum_congr rfl
    intro i hi
    have h : i < laterCount .h2452 + 1 := mem_range.mp hi
    change dotQ (fun k => running (tariffWeights false) (i+1) k - running (tariffWeights false) i k)
      (history .h2452 i) = _
    rw [register_eq false (i+1) (by omega),register_eq false i (by omega),history_eq i (by omega)]
    exact seed_charge_eq ⟨i,h⟩
  · decide +kernel

private abbrev count := laterCount Band.h2452+1
private def stepCost (i : ℕ) (k : Fin 4) : ℚ := registry true (i+1) k - registry true i k

private theorem step_nonneg (i : ℕ) (hi : i ∈ range count) (k : Fin 4) : 0 ≤ stepCost i k := by
  rw [stepCost, ← register_step true ⟨i,mem_range.mp hi⟩ k]
  exact sub_nonneg.mpr (le_max_left _ _)

private def prefersExit (i : ℕ) (k : Fin 4) (pivot : ℚ) : Prop :=
  i < stopIndex .h2452 ∨ rankReceipt k - pivot ≤ receipt i k

private instance (i : ℕ) (k : Fin 4) (pivot : ℚ) : Decidable (prefersExit i k pivot) := by
  unfold prefersExit
  infer_instance

private def intercept (k : Fin 4) (offset pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, stepCost i k * (if prefersExit i k pivot then
    (if i < stopIndex .h2452 then receipt i k else rankReceipt k) + offset else receipt i k)

private def gradient (k : Fin 4) (pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, if prefersExit i k pivot then stepCost i k else 0

private theorem bound_coordinate (k : Fin 4) (offset pivot x : ℚ) (used : Mass)
    (hx : used k = x-offset) :
    (∑ i ∈ range count, stepCost i k *
      remainder (stopIndex .h2452) receipt rankReceipt used i k) ≤
      intercept k offset pivot - gradient k pivot * x := by
  unfold intercept gradient
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_le_sum
  intro i hi
  by_cases ht : i < stopIndex .h2452
  · have hs : prefersExit i k pivot := Or.inl ht
    simp only [remainder, ite_eq_left ht, ite_eq_left hs, hx]
    ring_nf
    exact le_rfl
  · simp only [remainder, ite_eq_right ht, hx]
    by_cases hs : prefersExit i k pivot
    · simp only [ite_eq_left hs]
      have h := mul_le_mul_of_nonneg_left (min_le_right (receipt i k) (rankReceipt k-(x-offset)))
        (step_nonneg i hi k)
      convert h using 1
      ring
    · simp only [ite_eq_right hs, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (step_nonneg i hi k)

private theorem bill_by_coordinates (used : Mass) :
    weightedBill count (lossWeight .h2452 rate0 rate1)
      (remainder (stopIndex .h2452) (history .h2452) (rankMass .h2452) used) =
      ∑ k : Fin 4, ∑ i ∈ range count, stepCost i k *
        remainder (stopIndex .h2452) receipt rankReceipt used i k := by
  unfold weightedBill
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i < count := mem_range.mp hi
  have h₀ := register_eq true i (by omega : i ≤ count)
  have h₁ := register_eq true (i+1) (by omega : i+1 ≤ count)
  change dotQ (fun k => running (tariffWeights true) (i+1) k - running (tariffWeights true) i k)
    (remainder (stopIndex .h2452) (history .h2452) (rankMass .h2452) used i) = _
  rw [h₀,h₁]
  unfold dotQ
  apply sum_congr rfl
  intro k _
  unfold stepCost remainder
  rw [history_eq i (Nat.le_of_lt_succ hi'),rank_eq]

private theorem seed_and_static : intercept 0 0 0 + intercept 3 0 0 + seedCredit = (687328793175311486669206252487984823557424960091703/34413423078186733732484347136430000) := by
  decide +kernel

private theorem bill_and_fee {B J : ℕ} (pb pj cb cj mb mj : ℚ)
    (hb : intercept 2 2 pb = cb) (hb' : gradient 2 pb = mb)
    (hj : intercept 1 1 pj = cj) (hj' : gradient 1 pj = mj) :
    weightedBill count (lossWeight .h2452 rate0 rate1)
      (remainder (stopIndex .h2452) (history .h2452) (rankMass .h2452)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2452 +
      charge (lambdaDegree .h2452) (High52JointRank.mu .h2452) 0 0 0 B J ≤
      charge (lambdaDegree .h2452) (High52JointRank.mu .h2452) ((687328793175311486669206252487984823557424960091703/34413423078186733732484347136430000) + cb + cj) mb mj B J := by
  let used : Mass := ![0,(J : ℚ)-1,(B : ℚ)-2,0]
  have h0 := bound_coordinate 0 0 0 0 used (by simp [used])
  have h1 := bound_coordinate 1 1 pj J used (by rfl)
  have h2 := bound_coordinate 2 2 pb B used (by rfl)
  have h3 := bound_coordinate 3 0 0 0 used (by simp [used])
  change weightedBill count (lossWeight .h2452 rate0 rate1)
    (remainder (stopIndex .h2452) (history .h2452) (rankMass .h2452) used) + seedLimit .h2452 + _ ≤ _
  rw [bill_by_coordinates,seed_exact,Fin.sum_univ_four]
  rw [hb,hb'] at h2
  rw [hj,hj'] at h1
  unfold charge
  linarith only [h0,h1,h2,h3,seed_and_static]

private theorem b0 : intercept 2 2 43031 = (1687830322733868577149181240247/108727593195375) ∧
    gradient 2 43031 = 18832995480 := by decide +kernel

private theorem b1 : intercept 2 2 (8345060/49) = (1690363530435857798389570954247/108727593195375) ∧
    gradient 2 (8345060/49) = 19103708721 := by decide +kernel

private theorem b2 : intercept 2 2 (3236449067/11858) = (1690363536580178261209502269247/108727593195375) ∧
    gradient 2 (3236449067/11858) = 19103708943 := by decide +kernel

private theorem b3 : intercept 2 2 (8146467139/27225) = (13969946719951272908822165657/898575150375) ∧
    gradient 2 (8146467139/27225) = 19103709465 := by decide +kernel

private theorem b4 : intercept 2 2 (352387517/1125) = (15834713638812254106593317142/898575150375) ∧
    gradient 2 (352387517/1125) = 25860352702 := by decide +kernel

private theorem b5 : intercept 2 2 (55072924227/171125) = (161825547808647884662995892/7188601203) ∧
    gradient 2 (55072924227/171125) = 41171799948 := by decide +kernel

private theorem b6 : intercept 2 2 (1070695049247/3286969) = (128534743441772013512668/5250987) ∧
    gradient 2 (1070695049247/3286969) = 47235935828 := by decide +kernel

private theorem b7 : intercept 2 2 (3452328759317/10501974) = (96537538176479584288/2187) ∧
    gradient 2 (3452328759317/10501974) = 107340849512 := by decide +kernel

private theorem b8 : intercept 2 2 (756164782/2187) = 101589418059684984 ∧
    gradient 2 (756164782/2187) = 281258424954 := by decide +kernel

private theorem j0 : intercept 1 1 (64967/9) = (4463617956054838719162823626489037/241996457122914375) ∧
    gradient 1 (64967/9) = 107284516923 := by decide +kernel

private theorem j1 : intercept 1 1 (3415193/144) = (4483617328488318814587090031704037/241996457122914375) ∧
    gradient 1 (3415193/144) = 113008482067 := by decide +kernel

private theorem j2 : intercept 1 1 (6136073/144) = (36893881576963261066121571642647921/1935971656983315000) ∧
    gradient 1 (6136073/144) = 129052923242 := by decide +kernel

private theorem j3 : intercept 1 1 (9237005/162) = (39496621405359774560011468362077921/1935971656983315000) ∧
    gradient 1 (9237005/162) = 154794043508 := by decide +kernel

private theorem j4 : intercept 1 1 (1016294347/15876) = (569747784619974053828291246096641/23900884654115000) ∧
    gradient 1 (1016294347/15876) = 210390809013 := by decide +kernel

private theorem j5 : intercept 1 1 (4763914461/70756) = (96686031337212416065798334419163/3414412093445000) ∧
    gradient 1 (4763914461/70756) = 278030452448 := by decide +kernel

private theorem j6 : intercept 1 1 (23972519037/346921) = (362480326040677416996309097283/9458205245000) ∧
    gradient 1 (23972519037/346921) = 424252917068 := by decide +kernel

private theorem j7 : intercept 1 1 (142627986443/2033476) = (466285727659107735188490403/9842045000) ∧
    gradient 1 (142627986443/2033476) = 554011426896 := by decide +kernel

private theorem j8 : intercept 1 1 (556547968569/7873636) = (1205452752491983531132307/18605000) ∧
    gradient 1 (556547968569/7873636) = 800969417080 := by decide +kernel

private theorem j9 : intercept 1 1 (5286016996927/74420000) = (430673560242480523067/5000) ∧
    gradient 1 (5286016996927/74420000) = 1102191746999 := by decide +kernel

private theorem j10 : intercept 1 1 (1468929287/20000) = 129230396696703496 ∧
    gradient 1 (1468929287/20000) = 1707409321117 := by decide +kernel

private theorem checked_bound (B J : ℕ) (hB₀ : 2 ≤ B) (hJ₀ : 1 ≤ J)
    (hB₁ : B ≤ capB .h2452) (hJ₁ : J ≤ capJ .h2452) :
    weightedBill count (lossWeight .h2452 rate0 rate1)
      (remainder (stopIndex .h2452) (history .h2452) (rankMass .h2452)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2452 +
      charge (lambdaDegree .h2452) (High52JointRank.mu .h2452) 0 0 0 B J ≤ (fees .h2452).loss := by
  have hL : 0 ≤ lambdaDegree .h2452 := by unfold lambdaDegree; positivity
  have hBmax : capB .h2452 = 361196 := by decide +kernel
  have groupsB : (2 ≤ B ∧ B ≤ 86064) ∨ (86064 ≤ B ∧ B ≤ 254554) ∨ (254555 ≤ B ∧ B ≤ 291316) ∨ (291317 ≤ B ∧ B ≤ 307141) ∨ (307142 ≤ B ∧ B ≤ 319328) ∨ (319329 ≤ B ∧ B ≤ 324332) ∨ (324333 ≤ B ∧ B ≤ 327150) ∨ (327151 ≤ B ∧ B ≤ 330316) ∨ (330317 ≤ B ∧ B ≤ 361196) := by omega
  have hJmax : capJ .h2452 = 75688 := by decide +kernel
  have groupsJ : (1 ≤ J ∧ J ≤ 14438) ∨ (14439 ≤ J ∧ J ≤ 32997) ∨ (32998 ≤ J ∧ J ≤ 52228) ∨ (52229 ≤ J ∧ J ≤ 61810) ∨ (61811 ≤ J ∧ J ≤ 66220) ∨ (66221 ≤ J ∧ J ≤ 68439) ∨ (68440 ≤ J ∧ J ≤ 69764) ∨ (69765 ≤ J ∧ J ≤ 70517) ∨ (70518 ≤ J ∧ J ≤ 70854) ∨ (70855 ≤ J ∧ J ≤ 71206) ∨ (71207 ≤ J ∧ J ≤ 75688) := by omega
  rcases groupsB with ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩
  all_goals rcases groupsJ with ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 1) (J₁ := 14438)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 14439) (P₁ := 14439) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 32998) (P₁ := 32998) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 52229) (P₁ := 52229) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 86064) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 1) (J₁ := 14438)
      (P₀ := 1) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 14439) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 32998) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 52229) (P₁ := (60285986628309636991/1081234202558464)) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 86064) (B₁ := 254554) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 52229) (J₁ := 61810)
      (P₀ := (60287067862512195455/1081234202558464)) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 254555) (B₁ := 291316) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 291317) (B₁ := 307141) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 307142) (B₁ := 319328) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 319329) (B₁ := 324332) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 324333) (B₁ := 327150) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 61811) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 327151) (B₁ := 330316) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 1) (J₁ := 14438)
      (P₀ := 14438) (P₁ := 14438) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 14439) (J₁ := 32997)
      (P₀ := 32997) (P₁ := 32997) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 32998) (J₁ := 52228)
      (P₀ := 52228) (P₁ := 52228) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 52229) (J₁ := 61810)
      (P₀ := 61810) (P₁ := 61810) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 61811) (J₁ := 66220)
      (P₀ := 61811) (P₁ := 66220) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 66221) (J₁ := 68439)
      (P₀ := 66221) (P₁ := 66221) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 68440) (J₁ := 69764)
      (P₀ := 68440) (P₁ := 68440) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 69765) (J₁ := 70517)
      (P₀ := 69765) (P₁ := 69765) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 70518) (J₁ := 70854)
      (P₀ := 70518) (P₁ := 70518) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 70855) (J₁ := 71206)
      (P₀ := 70855) (P₁ := 70855) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 330317) (B₁ := 361196) (J₀ := 71207) (J₁ := 75688)
      (P₀ := 71207) (P₁ := 71207) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem loss_ledger (b : Band) : LossLedger b := by
  cases b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [seed_exact]; decide +kernel
  · decide +kernel
  · intro _
    refine ⟨rate0, rate1, ?_, checked_bound⟩
    intro i hi
    refine ⟨rate_valid ⟨i,by omega⟩, ?_⟩
    rw [seed_exact,history_eq i hi]
    have H : ∀ i : Fin count,
        min seedCredit (dotQ (cutWeight .h2452 0 i) (receipt i)) ≤ rate0 i := by
      decide +kernel
    exact H ⟨i,Nat.lt_succ_of_le hi⟩
  · decide +kernel
  · intro hi
    exact ((by decide : ¬ 7773 ≤ start .h2452) hi).elim

#print axioms schedule
#print axioms loss_ledger
end High52
