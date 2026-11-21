import ProximityPrize.SubmissionLower.Rect52PrefixScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Rect52Prefix

open Finset
open Rect52Prefix_3
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
open Rect52PrefixJointRank (capB capJ lambdaDegree)

private def historyTable : List Mass := [![6302, 97828, 475027, 3137519],
  ![6302, 97828, 475027, 3137519],
  ![3295, (638749/9), (2965975/9), (7769800/3)],
  ![(8865/4), (186183/4), (2965975/9), 1846881],
  ![(22201/18), (56523/2), (4715634/25), (35577369/25)],
  ![(59805/64), (161885/8), 136286, (43191168/49)],
  ![(86023/121), (1747587/121), (2695126/27), (6351905/9)],
  ![(127990/289), (3055940/289), (14384680/169), (6351905/9)],
  ![(127990/289), (3055940/289), (14384680/169), (1083697/3)],
  ![(203167/529), (219479/23), (3857245/54), (1083697/3)],
  ![(81205/256), (514345/64), (37974748/625), (1083697/3)],
  ![(68225/289), (514345/64), (37974748/625), (1083697/3)],
  ![(1018228/5043), (514345/64), (37974748/625), (1083697/3)],
  ![(1018228/5043), (1410803/192), (5809104/121), (2502724/9)],
  ![(1018228/5043), (32412384/5329), (3067753/75), (262631538/961)],
  ![(1018228/5043), (67451788/11881), (306848479/8100), (460111732/2209)],
  ![(1018228/5043), (30662924/5625), (50333088/1369), (460111732/2209)]]

private def rankReceipt : Mass := ![6302, 97828, 475027, (7769800/3)]

private def receipt (i : ℕ) : Mass := historyTable[i]?.getD (fun _ => 0)

private theorem receipt_zero : history .h2391 0 = receipt 0 := by
  funext k
  fin_cases k <;> decide +kernel

private theorem receipt_check :
    ∀ i : Fin (laterCount .h2391), ∀ k : Fin 4,
      capMin (receipt i) (stageCap .h2391 (i+1) (decide (stopIndex .h2391 ≤ i+1))) k =
        receipt (i+1) k := by
  intro i k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (i : ℕ) (hi : i ≤ laterCount .h2391) :
    history .h2391 i = receipt i := by
  induction i with
  | zero => exact receipt_zero
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount .h2391)]
    funext k
    exact receipt_check ⟨i,by omega⟩ k

private theorem rank_eq : rankMass .h2391 = rankReceipt := by
  funext k
  fin_cases k <;> decide +kernel

private def rate0 (i : ℕ) : ℚ := ([217415849, 235080308, 215363893, 178356579, 146945236, 129133696, 108297216, 109021588, 85672030, 77134596, 69356969, 87098186, 76568142, 101328371, 131992501, 168728078, 173568197] : List ℚ)[i]?.getD 0
private def rate1 (i : ℕ) : ℚ := ([1715321, 1570153, 1732184, 2130533, 2616481, 3006819, 3635482, 3610347, 4643071, 5181436, 5780194, 4559594, 5220539, 3896822, 2944168, 2254478, 2188248] : List ℚ)[i]?.getD 0
private def optimum (i : ℕ) : ℕ := ([5, 5, 5, 6, 7, 8, 10, 10, 13, 14, 16, 12, 14, 11, 8, 7, 6] : List ℕ)[i]?.getD 0

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


private theorem rate_valid (i : Fin (laterCount .h2391+1)) : RateOK (finish .h2391) (rate0 i) (rate1 i) := by
  apply rate_of_check (m := optimum i)
  fin_cases i <;> decide +kernel

private def seedRegisterTable : List Mass := [![0, 0, 0, 0],
  ![18864, 442, 116, 0],
  ![18864, 533, 142, 0],
  ![19781, 590, 155, 0],
  ![24153, 625, 166, 0],
  ![26304, 737, 196, 0],
  ![30009, 901, 240, 0],
  ![39778, 1131, 304, 0],
  ![39778, 1147, 305, 0],
  ![50283, 1448, 385, 0],
  ![63914, 1843, 490, 0],
  ![99341, 1843, 490, 0],
  ![163749, 1843, 490, 0],
  ![163749, 2340, 615, 0],
  ![163749, 3713, 987, 0],
  ![184432, 5545, 1492, 0],
  ![251561, 7488, 1991, 0],
  ![341710, 7488, 1991, 0]]

private def lossRegisterTable : List Mass := [![0, 0, 0, 0],
  ![4101332575536, 128455620602, 25220238484, 198977236],
  ![4307846644100, 154070857889, 33381403736, 222961726],
  ![4307846644100, 161329028574, 33381403736, 268488520],
  ![4307846644100, 162931625424, 33381403736, 353668478],
  ![4307846644100, 177122555156, 33381403736, 512830276],
  ![4307846644100, 206581091467, 33381403736, 721636560],
  ![4307846658048, 267096354292, 33381403736, 1105186528],
  ![4307846658048, 267096354292, 33381403736, 1105186528],
  ![4307846684490, 357520638533, 33381403736, 1787582335],
  ![4929980568744, 473325360932, 37795952040, 2538903640],
  ![6889990657429, 682684551670, 37795952040, 2538903640],
  ![14262240859314, 890776455736, 38758692770, 2538903640],
  ![14262240859314, 890776455736, 47089407330, 3210631485],
  ![14262240859314, 890776455736, 100011102177, 3846163314],
  ![24343640944432, 1274897210621, 196932811492, 4392698656],
  ![42445404029758, 1830574588222, 335937603298, 4488665698],
  ![59309988596870, 1930439918438, 335937603298, 4488665698]]

private def seedChargeTable : List ℚ := [217224036, 21253050, (102160003/9), (537970565/36), (114770683/10), (817752021/64), (54413255563/3267), (12420434280/48841), (715252820010/48841), (157156940831/9522), (2876849535/256), (4394235800/289), (3708531197/320), (649290378895/23232), (4833986987189497/134370735), (7035228045464638981/161772884100), (91792235972/5043)]

private def seedCredit : ℚ := (7851780753746479717936947979871009/15680659594589186103878400)

open High50Nonlinear (remainder charge charge_over_range)

private def tariffWeights (mode : Bool) : ℕ → Mass :=
  if mode then lossWeight .h2391 rate0 rate1 else cutWeight .h2391 0

private def registry (mode : Bool) (i : ℕ) : Mass :=
  ((if mode then lossRegisterTable else seedRegisterTable)[i]?).getD (fun _ => 0)

private theorem register_step (mode : Bool) :
    ∀ i : Fin (laterCount .h2391+1), ∀ k : Fin 4,
      max (registry mode i k) (tariffWeights mode i k) = registry mode (i+1) k := by
  cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (mode : Bool) (i : ℕ) (hi : i ≤ laterCount .h2391+1) :
    running (tariffWeights mode) i = registry mode i := by
  induction i with
  | zero => funext k; cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount .h2391+1)]
    exact register_step mode ⟨i,by omega⟩ k

private def seedCharge (i : ℕ) : ℚ := seedChargeTable[i]?.getD 0

private theorem seed_charge_eq : ∀ i : Fin (laterCount .h2391+1),
    dotQ (fun k => registry false (i+1) k - registry false i k) (receipt i) = seedCharge i := by
  intro i
  fin_cases i <;> decide +kernel

private theorem seed_exact : seedLimit .h2391 = seedCredit := by
  unfold seedLimit weightedBill
  trans (∑ i ∈ range (laterCount .h2391+1), seedCharge i)
  · apply sum_congr rfl
    intro i hi
    have h : i < laterCount .h2391 + 1 := mem_range.mp hi
    change dotQ (fun k => running (tariffWeights false) (i+1) k - running (tariffWeights false) i k)
      (history .h2391 i) = _
    rw [register_eq false (i+1) (by omega),register_eq false i (by omega),history_eq i (by omega)]
    exact seed_charge_eq ⟨i,h⟩
  · decide +kernel

private abbrev count := laterCount Band.h2391+1
private def stepCost (i : ℕ) (k : Fin 4) : ℚ := registry true (i+1) k - registry true i k

private theorem step_nonneg (i : ℕ) (hi : i ∈ range count) (k : Fin 4) : 0 ≤ stepCost i k := by
  rw [stepCost, ← register_step true ⟨i,mem_range.mp hi⟩ k]
  exact sub_nonneg.mpr (le_max_left _ _)

private def prefersExit (i : ℕ) (k : Fin 4) (pivot : ℚ) : Prop :=
  i < stopIndex .h2391 ∨ rankReceipt k - pivot ≤ receipt i k

private instance (i : ℕ) (k : Fin 4) (pivot : ℚ) : Decidable (prefersExit i k pivot) := by
  unfold prefersExit
  infer_instance

private def intercept (k : Fin 4) (offset pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, stepCost i k * (if prefersExit i k pivot then
    (if i < stopIndex .h2391 then receipt i k else rankReceipt k) + offset else receipt i k)

private def gradient (k : Fin 4) (pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, if prefersExit i k pivot then stepCost i k else 0

private theorem bound_coordinate (k : Fin 4) (offset pivot x : ℚ) (used : Mass)
    (hx : used k = x-offset) :
    (∑ i ∈ range count, stepCost i k *
      remainder (stopIndex .h2391) receipt rankReceipt used i k) ≤
      intercept k offset pivot - gradient k pivot * x := by
  unfold intercept gradient
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_le_sum
  intro i hi
  by_cases ht : i < stopIndex .h2391
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
    weightedBill count (lossWeight .h2391 rate0 rate1)
      (remainder (stopIndex .h2391) (history .h2391) (rankMass .h2391) used) =
      ∑ k : Fin 4, ∑ i ∈ range count, stepCost i k *
        remainder (stopIndex .h2391) receipt rankReceipt used i k := by
  unfold weightedBill
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i < count := mem_range.mp hi
  have h₀ := register_eq true i (by omega : i ≤ count)
  have h₁ := register_eq true (i+1) (by omega : i+1 ≤ count)
  change dotQ (fun k => running (tariffWeights true) (i+1) k - running (tariffWeights true) i k)
    (remainder (stopIndex .h2391) (history .h2391) (rankMass .h2391) used i) = _
  rw [h₀,h₁]
  unfold dotQ
  apply sum_congr rfl
  intro k _
  unfold stepCost remainder
  rw [history_eq i (Nat.le_of_lt_succ hi'),rank_eq]

private theorem seed_and_static : intercept 0 0 0 + intercept 3 0 0 + seedCredit = (16966382083357794858276082067383548320163644564429/407773988611497224360043930129600) := by
  decide +kernel

private theorem bill_and_fee {B J : ℕ} (pb pj cb cj mb mj : ℚ)
    (hb : intercept 2 2 pb = cb) (hb' : gradient 2 pb = mb)
    (hj : intercept 1 1 pj = cj) (hj' : gradient 1 pj = mj) :
    weightedBill count (lossWeight .h2391 rate0 rate1)
      (remainder (stopIndex .h2391) (history .h2391) (rankMass .h2391)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2391 +
      charge (lambdaDegree .h2391) (Rect52PrefixJointRank.mu .h2391) 0 0 0 B J ≤
      charge (lambdaDegree .h2391) (Rect52PrefixJointRank.mu .h2391) ((16966382083357794858276082067383548320163644564429/407773988611497224360043930129600) + cb + cj) mb mj B J := by
  let used : Mass := ![0,(J : ℚ)-1,(B : ℚ)-2,0]
  have h0 := bound_coordinate 0 0 0 0 used (by simp [used])
  have h1 := bound_coordinate 1 1 pj J used (by rfl)
  have h2 := bound_coordinate 2 2 pb B used (by rfl)
  have h3 := bound_coordinate 3 0 0 0 used (by simp [used])
  change weightedBill count (lossWeight .h2391 rate0 rate1)
    (remainder (stopIndex .h2391) (history .h2391) (rankMass .h2391) used) + seedLimit .h2391 + _ ≤ _
  rw [bill_by_coordinates,seed_exact,Fin.sum_univ_four]
  rw [hb,hb'] at h2
  rw [hj,hj'] at h1
  unfold charge
  linarith only [h0,h1,h2,h3,seed_and_static]

private theorem b0 : intercept 2 2 (21794213/108) = (7761340212458735167967/272250) ∧
    gradient 2 (21794213/108) = 33381403736 := by decide +kernel

private theorem b1 : intercept 2 2 (27602907983/67500) = (24739228389837851961901/816750) ∧
    gradient 2 (27602907983/67500) = 37795952040 := by decide +kernel

private theorem b2 : intercept 2 2 (31811099621/75625) = (5576742226724031173669/163350) ∧
    gradient 2 (31811099621/75625) = 47089407330 := by decide +kernel

private theorem b3 : intercept 2 2 (7814859137/18150) = (76596909756840552239/1350) ∧
    gradient 2 (7814859137/18150) = 100011102177 := by decide +kernel

private theorem b4 : intercept 2 2 (7057271597/16200) = (133399776778712038979/1350) ∧
    gradient 2 (7057271597/16200) = 196932811492 := by decide +kernel

private theorem b5 : intercept 2 2 (7388588921/16200) = 159580103757045642 ∧
    gradient 2 (7388588921/16200) = 335937603298 := by decide +kernel

private theorem j0 : intercept 1 1 (241703/18) = (44279802075640614612029948679115399/1527675170119890000) ∧
    gradient 1 (241703/18) = 154070857889 := by decide +kernel

private theorem j1 : intercept 1 1 (2812973/72) = (133732784022351427976726892370946197/4583025510359670000) ∧
    gradient 1 (2812973/72) = 161329028574 := by decide +kernel

private theorem j2 : intercept 1 1 (483395/8) = (134109446275157687384711342309321197/4583025510359670000) ∧
    gradient 1 (483395/8) = 162931625424 := by decide +kernel

private theorem j3 : intercept 1 1 (1177271/16) = (138633935111118354410636206709021197/4583025510359670000) ∧
    gradient 1 (1177271/16) = 177122555156 := by decide +kernel

private theorem j4 : intercept 1 1 (155826227/1936) = (149109756411720019892057907645944947/4583025510359670000) ∧
    gradient 1 (155826227/1936) = 206581091467 := by decide +kernel

private theorem j5 : intercept 1 1 (5967073281/69938) = (1423440627470344744000307124392107/37876243887270000) ∧
    gradient 1 (5967073281/69938) = 267096354292 := by decide +kernel

private theorem j6 : intercept 1 1 (1166809381/13294) = (5959454845681167284017108575163/131059667430000) ∧
    gradient 1 (1166809381/13294) = 357520638533 := by decide +kernel

private theorem j7 : intercept 1 1 (262129041/2944) = (317365524349290306284665717181/5698246410000) ∧
    gradient 1 (262129041/2944) = 473325360932 := by decide +kernel

private theorem j8 : intercept 1 1 (61914315655/682112) = (33184883103948796607403109316/356140400625) ∧
    gradient 1 (61914315655/682112) = 890776455736 := by decide +kernel

private theorem j9 : intercept 1 1 (5821596163694/63313849) = (8582458430265664088637629/66830625) ∧
    gradient 1 (5821596163694/63313849) = 1274897210621 := by decide +kernel

private theorem j10 : intercept 1 1 (6166045128728/66830625) = (1010405620855979575334/5625) ∧
    gradient 1 (6166045128728/66830625) = 1830574588222 := by decide +kernel

private theorem j11 : intercept 1 1 (534951038/5625) = 188853006780871102 ∧
    gradient 1 (534951038/5625) = 1930439918438 := by decide +kernel

private theorem checked_bound (B J : ℕ) (hB₀ : 2 ≤ B) (hJ₀ : 1 ≤ J)
    (hB₁ : B ≤ capB .h2391) (hJ₁ : J ≤ capJ .h2391) :
    weightedBill count (lossWeight .h2391 rate0 rate1)
      (remainder (stopIndex .h2391) (history .h2391) (rankMass .h2391)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2391 +
      charge (lambdaDegree .h2391) (Rect52PrefixJointRank.mu .h2391) 0 0 0 B J ≤ (fees .h2391).loss := by
  have hL : 0 ≤ lambdaDegree .h2391 := by unfold lambdaDegree; positivity
  have hBmax : capB .h2391 = 475029 := by decide +kernel
  have groupsB : (2 ≤ B ∧ B ≤ 403598) ∨ (403599 ≤ B ∧ B ≤ 414269) ∨ (414270 ≤ B ∧ B ≤ 427019) ∨ (427020 ≤ B ∧ B ≤ 434125) ∨ (434126 ≤ B ∧ B ≤ 437146) ∨ (437147 ≤ B ∧ B ≤ 475029) := by omega
  have hJmax : capJ .h2391 = 97829 := by decide +kernel
  have groupsJ : (1 ≤ J ∧ J ≤ 26856) ∨ (26857 ≤ J ∧ J ≤ 51283) ∨ (51284 ≤ J ∧ J ≤ 69567) ∨ (69568 ≤ J ∧ J ≤ 77593) ∨ (77594 ≤ J ∧ J ≤ 83386) ∨ (83387 ≤ J ∧ J ≤ 87254) ∨ (87255 ≤ J ∧ J ≤ 88286) ∨ (88287 ≤ J ∧ J ≤ 89792) ∨ (89793 ≤ J ∧ J ≤ 91746) ∨ (91747 ≤ J ∧ J ≤ 92151) ∨ (92152 ≤ J ∧ J ≤ 92377) ∨ (92378 ≤ J ∧ J ≤ 97829) := by omega
  rcases groupsB with ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩
  all_goals rcases groupsJ with ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 1) (J₁ := 26856)
      (P₀ := 1) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 26857) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 51284) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 69568) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 77594) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 83387) (J₁ := 87254)
      (P₀ := 83387) (P₁ := 83387) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 403598) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 1) (J₁ := 26856)
      (P₀ := 26856) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 51283) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 69567) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 77593) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 83386) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 83387) (J₁ := 87254)
      (P₀ := 83387) (P₁ := 83387) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 403599) (B₁ := 414269) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 1) (J₁ := 26856)
      (P₀ := 26856) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 51283) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 69567) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 77593) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 83386) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 83387) (J₁ := 87254)
      (P₀ := 83387) (P₁ := (137232063445921839/1637415387136)) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 414270) (B₁ := 427019) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 1) (J₁ := 26856)
      (P₀ := 26856) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 51283) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 69567) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 77593) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 83386) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 83387) (J₁ := 87254)
      (P₀ := (137233700861308975/1637415387136)) (P₁ := 87254) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 427020) (B₁ := 434125) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 1) (J₁ := 26856)
      (P₀ := 26856) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 51283) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 69567) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 77593) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 83386) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 83387) (J₁ := 87254)
      (P₀ := 87254) (P₁ := 87254) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 434126) (B₁ := 437146) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 1) (J₁ := 26856)
      (P₀ := 26856) (P₁ := 26856) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 26857) (J₁ := 51283)
      (P₀ := 51283) (P₁ := 51283) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 51284) (J₁ := 69567)
      (P₀ := 69567) (P₁ := 69567) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 69568) (J₁ := 77593)
      (P₀ := 77593) (P₁ := 77593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 77594) (J₁ := 83386)
      (P₀ := 83386) (P₁ := 83386) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 83387) (J₁ := 87254)
      (P₀ := 87254) (P₁ := 87254) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 87255) (J₁ := 88286)
      (P₀ := 87255) (P₁ := 87255) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 88287) (J₁ := 89792)
      (P₀ := 88287) (P₁ := 88287) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 89793) (J₁ := 91746)
      (P₀ := 89793) (P₁ := 89793) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 91747) (J₁ := 92151)
      (P₀ := 91747) (P₁ := 91747) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 92152) (J₁ := 92377)
      (P₀ := 92152) (P₁ := 92152) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 437147) (B₁ := 475029) (J₀ := 92378) (J₁ := 97829)
      (P₀ := 92378) (P₁ := 92378) hL
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
        min seedCredit (dotQ (cutWeight .h2391 0 i) (receipt i)) ≤ rate0 i := by
      decide +kernel
    exact H ⟨i,Nat.lt_succ_of_le hi⟩
  · decide +kernel
  · intro hi
    exact ((by decide : ¬ 7773 ≤ start .h2391) hi).elim

#print axioms schedule
#print axioms loss_ledger
end Rect52Prefix
