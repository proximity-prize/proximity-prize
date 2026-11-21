import ProximityPrize.SubmissionLower.High55Wide2524ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High55Wide2524

open Finset
open High55Wide2524_3
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
open High55Wide2524JointRank (capB capJ lambdaDegree)

private def historyTable : List Mass := [![6436, 71867, 343541, 1755887],
  ![4451, 71867, 343541, 1755887],
  ![(35767/9), (178463/3), (822593/3), 1098888],
  ![2695, (332117/8), 268034, (1447225/2)],
  ![(53983/36), (275267/12), (3772191/25), (15896342/25)],
  ![(67168/81), (122318/9), (5117394/49), (6451515/16)],
  ![(57277/98), (915387/98), (8340925/121), (41165915/144)],
  ![(147903/361), (2578288/361), (3993991/75), (41165915/144)],
  ![(147903/361), (2578288/361), (3993991/75), (87480533/484)],
  ![(205091/841), (2578288/361), (3993991/75), (87480533/484)],
  ![(205091/841), (5654871/961), (25989931/625), (87480533/484)],
  ![(205091/841), (5457259/1058), (50345825/1369), (87480533/484)],
  ![(600622/3249), (5457259/1058), (50345825/1369), (87480533/484)],
  ![(600622/3249), (17950743/3721), (81571263/2401), (87480533/484)],
  ![(7646967/48223), (17950743/3721), (81571263/2401), (87480533/484)],
  ![(106945/726), (17950743/3721), (81571263/2401), (87480533/484)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)],
  ![(106945/726), (22443057/5000), (202925167/6561), (1224397603/7056)]]

private def rankReceipt : Mass := ![6436, 71867, 343541, 1755887]

private def receipt (i : ℕ) : Mass := historyTable[i]?.getD (fun _ => 0)

private theorem receipt_zero : history .h2524 0 = receipt 0 := by
  funext k
  fin_cases k <;> decide +kernel

private theorem receipt_check :
    ∀ i : Fin (laterCount .h2524), ∀ k : Fin 4,
      capMin (receipt i) (stageCap .h2524 (i+1) (decide (stopIndex .h2524 ≤ i+1))) k =
        receipt (i+1) k := by
  intro i k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (i : ℕ) (hi : i ≤ laterCount .h2524) :
    history .h2524 i = receipt i := by
  induction i with
  | zero => exact receipt_zero
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount .h2524)]
    funext k
    exact receipt_check ⟨i,by omega⟩ k

private theorem rank_eq : rankMass .h2524 = rankReceipt := by
  funext k
  fin_cases k <;> decide +kernel

private def rate0 (i : ℕ) : ℚ := ([150876953, 138970436, 126854375, 114334763, 93707501, 73662318, 60351041, 65228143, 56668911, 58375513, 65560191, 59190388, 59843139, 71948411, 91910421, 85049797, 710235478, 532676609, 303427838, 727772157, 710235478, 532676609, 236745160, 304386634, 193700585, 142047096, 125335673, 304386634, 133169153, 136872176] : List ℚ)[i]?.getD 0
private def rate1 (i : ℕ) : ℚ := ([2552986, 2793266, 3072726, 3428465, 4229513, 5436504, 6680375, 6162583, 7127089, 6907829, 6128539, 6814008, 6738852, 5572758, 4320158, 4683386, 389400, 584100, 1173104, 370171, 389400, 584100, 1557597, 1168198, 1946995, 2725793, 3115192, 1168198, 2920492, 2839282] : List ℚ)[i]?.getD 0
private def optimum (i : ℕ) : ℕ := ([7, 8, 9, 10, 12, 15, 18, 17, 19, 19, 16, 18, 18, 15, 12, 13, 2, 2, 4, 2, 2, 2, 5, 4, 6, 8, 9, 4, 8, 8] : List ℕ)[i]?.getD 0

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


private theorem rate_valid (i : Fin (laterCount .h2524+1)) : RateOK (finish .h2524) (rate0 i) (rate1 i) := by
  apply rate_of_check (m := optimum i)
  fin_cases i <;> decide +kernel

private def seedRegisterTable : List Mass := [![0, 0, 0, 0],
  ![12175, 445, 118, 0],
  ![13293, 489, 130, 0],
  ![14600, 521, 138, 0],
  ![16786, 612, 163, 0],
  ![20481, 717, 191, 0],
  ![26005, 942, 253, 0],
  ![31801, 1146, 305, 0],
  ![41519, 1346, 357, 0],
  ![47790, 1454, 385, 0],
  ![47790, 1662, 443, 0],
  ![65625, 2322, 628, 0],
  ![97191, 2360, 634, 0],
  ![97191, 2961, 788, 0],
  ![157812, 3099, 819, 0],
  ![207673, 3099, 819, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![207673, 4708, 1261, 0],
  ![229893, 8065, 2160, 0]]

private def lossRegisterTable : List Mass := [![0, 0, 0, 0],
  ![1836926902775, 98222848635, 17803480454, 301252348],
  ![1847334005748, 105087428142, 18066156680, 363124580],
  ![1852073875000, 110952928975, 18066156680, 424036188],
  ![1919223331718, 127523088446, 18636566369, 558839795],
  ![1919223331718, 153812933970, 18636566369, 807836983],
  ![1919223331718, 210766190076, 18636566454, 1375435512],
  ![1919223454841, 281604898361, 18636566454, 2037514375],
  ![2708207269217, 343661364055, 23286447051, 2200042131],
  ![2708207269217, 423000179904, 23286447051, 2743929265],
  ![2754973960522, 423028184432, 25860352259, 3060168247],
  ![4302387534375, 554416135377, 41171799948, 3848722492],
  ![5752773000108, 801949567208, 41171799948, 4320081072],
  ![5752773000108, 801949567208, 47156393532, 5310215376],
  ![11354322636732, 1102416211185, 58925748609, 5310215376],
  ![19087312860333, 1102416211185, 58925748609, 5310215376],
  ![19087312860333, 1102416211185, 107247794017, 5905749746],
  ![19087312860333, 1102416211185, 107247794017, 5905749746],
  ![19087312860333, 1102416211185, 107247794017, 5905749746],
  ![20072965195052, 1102416211185, 107247794017, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![20072965195052, 1102416211185, 145554431400, 5905749746],
  ![31465955157168, 1756605156266, 295643900160, 6132849120]]

private def seedChargeTable : List ℚ := [150876953, 12260858, (83622149/9), (130959607/8), (5478387889/450), (56017321786/3969), (52635021520/5929), (613431082/75), (130817872303/27075), (123847476358/27075), (55480356358568/3483625), (4942175401575265/609053041), (12693009489071/1448402), (125063089113225335/9675653043), (54469345941/6889), (203506259887653/8934121), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (16652232911734679/360855000)]

private def seedCredit : ℚ := (4698864776878476142333544037869978664572329/12905033654320025149681630176161250)

open High50Nonlinear (remainder charge charge_over_range)

private def tariffWeights (mode : Bool) : ℕ → Mass :=
  if mode then lossWeight .h2524 rate0 rate1 else cutWeight .h2524 0

private def registry (mode : Bool) (i : ℕ) : Mass :=
  ((if mode then lossRegisterTable else seedRegisterTable)[i]?).getD (fun _ => 0)

private theorem register_step (mode : Bool) :
    ∀ i : Fin (laterCount .h2524+1), ∀ k : Fin 4,
      max (registry mode i k) (tariffWeights mode i k) = registry mode (i+1) k := by
  cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (mode : Bool) (i : ℕ) (hi : i ≤ laterCount .h2524+1) :
    running (tariffWeights mode) i = registry mode i := by
  induction i with
  | zero => funext k; cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount .h2524+1)]
    exact register_step mode ⟨i,by omega⟩ k

private def seedCharge (i : ℕ) : ℚ := seedChargeTable[i]?.getD 0

private theorem seed_charge_eq : ∀ i : Fin (laterCount .h2524+1),
    dotQ (fun k => registry false (i+1) k - registry false i k) (receipt i) = seedCharge i := by
  intro i
  fin_cases i <;> decide +kernel

private theorem seed_exact : seedLimit .h2524 = seedCredit := by
  unfold seedLimit weightedBill
  trans (∑ i ∈ range (laterCount .h2524+1), seedCharge i)
  · apply sum_congr rfl
    intro i hi
    have h : i < laterCount .h2524 + 1 := mem_range.mp hi
    change dotQ (fun k => running (tariffWeights false) (i+1) k - running (tariffWeights false) i k)
      (history .h2524 i) = _
    rw [register_eq false (i+1) (by omega),register_eq false i (by omega),history_eq i (by omega)]
    exact seed_charge_eq ⟨i,h⟩
  · decide +kernel

private abbrev count := laterCount Band.h2524+1
private def stepCost (i : ℕ) (k : Fin 4) : ℚ := registry true (i+1) k - registry true i k

private theorem step_nonneg (i : ℕ) (hi : i ∈ range count) (k : Fin 4) : 0 ≤ stepCost i k := by
  rw [stepCost, ← register_step true ⟨i,mem_range.mp hi⟩ k]
  exact sub_nonneg.mpr (le_max_left _ _)

private def prefersExit (i : ℕ) (k : Fin 4) (pivot : ℚ) : Prop :=
  i < stopIndex .h2524 ∨ rankReceipt k - pivot ≤ receipt i k

private instance (i : ℕ) (k : Fin 4) (pivot : ℚ) : Decidable (prefersExit i k pivot) := by
  unfold prefersExit
  infer_instance

private def intercept (k : Fin 4) (offset pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, stepCost i k * (if prefersExit i k pivot then
    (if i < stopIndex .h2524 then receipt i k else rankReceipt k) + offset else receipt i k)

private def gradient (k : Fin 4) (pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, if prefersExit i k pivot then stepCost i k else 0

private theorem bound_coordinate (k : Fin 4) (offset pivot x : ℚ) (used : Mass)
    (hx : used k = x-offset) :
    (∑ i ∈ range count, stepCost i k *
      remainder (stopIndex .h2524) receipt rankReceipt used i k) ≤
      intercept k offset pivot - gradient k pivot * x := by
  unfold intercept gradient
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_le_sum
  intro i hi
  by_cases ht : i < stopIndex .h2524
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
    weightedBill count (lossWeight .h2524 rate0 rate1)
      (remainder (stopIndex .h2524) (history .h2524) (rankMass .h2524) used) =
      ∑ k : Fin 4, ∑ i ∈ range count, stepCost i k *
        remainder (stopIndex .h2524) receipt rankReceipt used i k := by
  unfold weightedBill
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i < count := mem_range.mp hi
  have h₀ := register_eq true i (by omega : i ≤ count)
  have h₁ := register_eq true (i+1) (by omega : i+1 ≤ count)
  change dotQ (fun k => running (tariffWeights true) (i+1) k - running (tariffWeights true) i k)
    (remainder (stopIndex .h2524) (history .h2524) (rankMass .h2524) used i) = _
  rw [h₀,h₁]
  unfold dotQ
  apply sum_congr rfl
  intro k _
  unfold stepCost remainder
  rw [history_eq i (Nat.le_of_lt_succ hi'),rank_eq]

private theorem seed_and_static : intercept 0 0 0 + intercept 3 0 0 + seedCredit = (999043520790713843665218169500684608454125554554241/51620134617280100598726520704645000) := by
  decide +kernel

private theorem bill_and_fee {B J : ℕ} (pb pj cb cj mb mj : ℚ)
    (hb : intercept 2 2 pb = cb) (hb' : gradient 2 pb = mb)
    (hj : intercept 1 1 pj = cj) (hj' : gradient 1 pj = mj) :
    weightedBill count (lossWeight .h2524 rate0 rate1)
      (remainder (stopIndex .h2524) (history .h2524) (rankMass .h2524)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2524 +
      charge (lambdaDegree .h2524) (High55Wide2524JointRank.mu .h2524) 0 0 0 B J ≤
      charge (lambdaDegree .h2524) (High55Wide2524JointRank.mu .h2524) ((999043520790713843665218169500684608454125554554241/51620134617280100598726520704645000) + cb + cj) mb mj B J := by
  let used : Mass := ![0,(J : ℚ)-1,(B : ℚ)-2,0]
  have h0 := bound_coordinate 0 0 0 0 used (by simp [used])
  have h1 := bound_coordinate 1 1 pj J used (by rfl)
  have h2 := bound_coordinate 2 2 pb B used (by rfl)
  have h3 := bound_coordinate 3 0 0 0 used (by simp [used])
  change weightedBill count (lossWeight .h2524 rate0 rate1)
    (remainder (stopIndex .h2524) (history .h2524) (rankMass .h2524) used) + seedLimit .h2524 + _ ≤ _
  rw [bill_by_coordinates,seed_exact,Fin.sum_univ_four]
  rw [hb,hb'] at h2
  rw [hj,hj'] at h1
  unfold charge
  linarith only [h0,h1,h2,h3,seed_and_static]

private theorem b0 : intercept 2 2 (75507/2) = (208505170296319008235086689156/13478627255625) ∧
    gradient 2 (75507/2) = 18066156680 := by decide +kernel

private theorem b1 : intercept 2 2 182897 = (209085709129742849958076632281/13478627255625) ∧
    gradient 2 182897 = 18636566369 := by decide +kernel

private theorem b2 : intercept 2 2 (602899/2) = (237350272689446833018806863156/13478627255625) ∧
    gradient 2 (602899/2) = 25860352259 := by decide +kernel

private theorem b3 : intercept 2 2 (656153/2) = 101566392392666880 ∧
    gradient 2 (656153/2) = 295643900160 := by decide +kernel

private theorem j0 : intercept 1 1 (12379/2) = (755970181587366961702248094843353/41826548144701250) ∧
    gradient 1 (12379/2) = 105087428142 := by decide +kernel

private theorem j1 : intercept 1 1 (61307/2) = (9360535028352148387249592837604611/501918577736415000) ∧
    gradient 1 (61307/2) = 127523088446 := by decide +kernel

private theorem j2 : intercept 1 1 (120795/2) = (3890691834134694625051911608996537/167306192578805000) ∧
    gradient 1 (120795/2) = 210766190076 := by decide +kernel

private theorem checked_bound (B J : ℕ) (hB₀ : 2 ≤ B) (hJ₀ : 1 ≤ J)
    (hB₁ : B ≤ capB .h2524) (hJ₁ : J ≤ capJ .h2524) :
    weightedBill count (lossWeight .h2524 rate0 rate1)
      (remainder (stopIndex .h2524) (history .h2524) (rankMass .h2524)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2524 +
      charge (lambdaDegree .h2524) (High55Wide2524JointRank.mu .h2524) 0 0 0 B J ≤ (fees .h2524).loss := by
  have hL : 0 ≤ lambdaDegree .h2524 := by unfold lambdaDegree; positivity
  have hBmax : capB .h2524 = 343543 := by decide +kernel
  have groupsB : (2 ≤ B ∧ B ≤ 75509) ∨ (75509 ≤ B ∧ B ≤ 290289) ∨ (290289 ≤ B ∧ B ≤ 312614) ∨ (312614 ≤ B ∧ B ≤ 343543) := by omega
  have hJmax : capJ .h2524 = 71868 := by decide +kernel
  have groupsJ : (1 ≤ J ∧ J ≤ 12380) ∨ (12380 ≤ J ∧ J ≤ 48929) ∨ (48929 ≤ J ∧ J ≤ 71868) := by omega
  rcases groupsB with ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩
  all_goals rcases groupsJ with ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 75509) (J₀ := 1) (J₁ := 12380)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 75509) (J₀ := 12380) (J₁ := 48929)
      (P₀ := 12380) (P₁ := 12380) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 75509) (J₀ := 48929) (J₁ := 71868)
      (P₀ := 48929) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 75509) (B₁ := 290289) (J₀ := 1) (J₁ := 12380)
      (P₀ := 1) (P₁ := 12380) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 75509) (B₁ := 290289) (J₀ := 12380) (J₁ := 48929)
      (P₀ := 12380) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 75509) (B₁ := 290289) (J₀ := 48929) (J₁ := 71868)
      (P₀ := 48929) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 290289) (B₁ := 312614) (J₀ := 1) (J₁ := 12380)
      (P₀ := 12380) (P₁ := 12380) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 290289) (B₁ := 312614) (J₀ := 12380) (J₁ := 48929)
      (P₀ := 48929) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 290289) (B₁ := 312614) (J₀ := 48929) (J₁ := 71868)
      (P₀ := 48929) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 312614) (B₁ := 343543) (J₀ := 1) (J₁ := 12380)
      (P₀ := 12380) (P₁ := 12380) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 312614) (B₁ := 343543) (J₀ := 12380) (J₁ := 48929)
      (P₀ := 48929) (P₁ := 48929) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 312614) (B₁ := 343543) (J₀ := 48929) (J₁ := 71868)
      (P₀ := 48929) (P₁ := 71868) hL
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
        min seedCredit (dotQ (cutWeight .h2524 0 i) (receipt i)) ≤ rate0 i := by
      decide +kernel
    exact H ⟨i,Nat.lt_succ_of_le hi⟩
  · decide +kernel
  · intro hi
    exact ((by decide : ¬ 7773 ≤ start .h2524) hi).elim

#print axioms schedule
#print axioms loss_ledger
end High55Wide2524
