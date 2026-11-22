import ProximityPrize.SubmissionLower.Peer653NativePrefixScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653NativePrefix

open Finset
open Peer653NativePrefix_3
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
open Peer653NativePrefixJointRank (capB capJ lambdaDegree)

private def historyTable : List Mass := [![7409, 97409, 476583, 2692638],
  ![7409, 97409, 476583, 2692638],
  ![(34519/9), (727276/9), (3330464/9), 2381728],
  ![(8997/4), (227349/4), 313456, 1774773],
  ![(41833/25), (215226/5), (4875043/16), 1461681],
  ![(13727/9), (280555/9), (5197028/25), (6448128/5)],
  ![(4029/4), (737013/32), (955841/7), (45784555/49)],
  ![(90802/121), (1935334/121), (2981086/27), (66430364/81)],
  ![(126326/289), (3473154/289), (16460788/169), (66430364/81)],
  ![(126326/289), (3473154/289), (16460788/169), (12708844/25)],
  ![(126326/289), (523363/49), (21201049/289), (18290989/54)],
  ![(142973/512), (10358209/1024), (21201049/289), (18290989/54)],
  ![(142973/512), (9339096/961), (41768095/676), (72818680/243)],
  ![(142973/512), 7720, (64229748/1225), (72818680/243)],
  ![(142973/512), (68170345/10082), (2613351/58), 277729],
  ![(516397/2592), (68170345/10082), (2613351/58), 277729],
  ![(516397/2592), (62046617/9801), (281220179/6561), (1935183594/7225)]]

private def rankReceipt : Mass := ![7409, 97409, 476583, 2381728]

private def receipt (i : ℕ) : Mass := historyTable[i]?.getD (fun _ => 0)

private theorem receipt_zero : history .h2390 0 = receipt 0 := by
  funext k
  fin_cases k <;> decide +kernel

private theorem receipt_check :
    ∀ i : Fin (laterCount .h2390), ∀ k : Fin 4,
      capMin (receipt i) (stageCap .h2390 (i+1) (decide (stopIndex .h2390 ≤ i+1))) k =
        receipt (i+1) k := by
  intro i k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (i : ℕ) (hi : i ≤ laterCount .h2390) :
    history .h2390 i = receipt i := by
  induction i with
  | zero => exact receipt_zero
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount .h2390)]
    funext k
    exact receipt_check ⟨i,by omega⟩ k

private theorem rank_eq : rankMass .h2390 = rankReceipt := by
  funext k
  fin_cases k <;> decide +kernel

private def rate0 (i : ℕ) : ℚ := ([254832819, 276233464, 208802454, 192355432, 152142872, 146945235, 129133695, 109576968, 160813369, 97831632, 88595102, 79384566, 90562886, 122339530, 122510846, 156992327, 164853428] : List ℚ)[i]?.getD 0
private def rate1 (i : ℕ) : ℚ := ([1421615, 1312116, 1787199, 1963002, 2531651, 2618082, 3008658, 3593273, 2387470, 4046810, 4486886, 5029191, 4387641, 3198613, 3193823, 2451010, 2320288] : List ℚ)[i]?.getD 0
private def optimum (i : ℕ) : ℕ := ([4, 4, 5, 6, 7, 8, 9, 10, 7, 11, 12, 14, 12, 9, 9, 7, 7] : List ℕ)[i]?.getD 0

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


private theorem rate_valid (i : Fin (laterCount .h2390+1)) : RateOK (finish .h2390) (rate0 i) (rate1 i) := by
  apply rate_of_check (m := optimum i)
  fin_cases i <;> decide +kernel

private def seedRegisterTable : List Mass := [![0, 0, 0, 0],
  ![19877, 478, 128, 0],
  ![20376, 557, 149, 0],
  ![24822, 557, 149, 0],
  ![26968, 577, 154, 0],
  ![26968, 704, 188, 0],
  ![29905, 751, 201, 0],
  ![33182, 948, 254, 0],
  ![46976, 1114, 298, 0],
  ![46976, 1114, 298, 0],
  ![49502, 1432, 383, 0],
  ![91441, 1606, 429, 0],
  ![91441, 1763, 472, 0],
  ![91441, 2478, 664, 0],
  ![139224, 3836, 1027, 0],
  ![234140, 3836, 1027, 0],
  ![234140, 5262, 1405, 0],
  ![373000, 5262, 1405, 0]]

private def lossRegisterTable : List Mass := [![0, 0, 0, 0],
  ![5065311943263, 150067528837, 32618600832, 181966720],
  ![5628533062464, 180597715064, 41158786136, 195505284],
  ![5628533062464, 180597715064, 41158786136, 257356656],
  ![5628533062464, 180597715064, 41158786136, 302302308],
  ![5628533062464, 180597715064, 41158786136, 475950388],
  ![5628533062464, 188649613695, 41158786136, 526234482],
  ![5628533062464, 222252032616, 41158786136, 764199132],
  ![5628533062464, 290866334800, 41158786136, 1070795354],
  ![5740876459931, 290866334800, 41158786136, 1070795354],
  ![5740876459931, 340420085644, 41158786136, 1549928230],
  ![8101224721982, 552569076538, 41158786136, 1924874094],
  ![8101224721982, 552569076538, 41158786136, 2373778152],
  ![8255350436216, 624374634504, 60133756304, 2913393624],
  ![17032598724720, 914618133392, 125642697310, 3284975551],
  ![28684689482440, 1119989667368, 125642697310, 3284975551],
  ![29700750375822, 1289790402534, 220574219435, 3443669050],
  ![61490328644000, 1700779743676, 224860075792, 3443669050]]

private def seedChargeTable : List ℚ := [254832819, 21400645, 17052386, (15061831/2), (633048271/40), (1945609376/225), (3376817111/224), (58363584128/3267), 0, (644941310932/48841), (333706315850/14161), (1403507606525/295936), (3055168351320/162409), (26881704918563/627200), (3392606317/128), (3899425775464/146189), (17926721855/648)]

private def seedCredit : ℚ := (1829761063094856071366045926271/3374341678848439563264)

open High50Nonlinear (remainder charge charge_over_range)

private def tariffWeights (mode : Bool) : ℕ → Mass :=
  if mode then lossWeight .h2390 rate0 rate1 else cutWeight .h2390 0

private def registry (mode : Bool) (i : ℕ) : Mass :=
  ((if mode then lossRegisterTable else seedRegisterTable)[i]?).getD (fun _ => 0)

private theorem register_step (mode : Bool) :
    ∀ i : Fin (laterCount .h2390+1), ∀ k : Fin 4,
      max (registry mode i k) (tariffWeights mode i k) = registry mode (i+1) k := by
  cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (mode : Bool) (i : ℕ) (hi : i ≤ laterCount .h2390+1) :
    running (tariffWeights mode) i = registry mode i := by
  induction i with
  | zero => funext k; cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount .h2390+1)]
    exact register_step mode ⟨i,by omega⟩ k

private def seedCharge (i : ℕ) : ℚ := seedChargeTable[i]?.getD 0

private theorem seed_charge_eq : ∀ i : Fin (laterCount .h2390+1),
    dotQ (fun k => registry false (i+1) k - registry false i k) (receipt i) = seedCharge i := by
  intro i
  fin_cases i <;> decide +kernel

private theorem seed_exact : seedLimit .h2390 = seedCredit := by
  unfold seedLimit weightedBill
  trans (∑ i ∈ range (laterCount .h2390+1), seedCharge i)
  · apply sum_congr rfl
    intro i hi
    have h : i < laterCount .h2390 + 1 := mem_range.mp hi
    change dotQ (fun k => running (tariffWeights false) (i+1) k - running (tariffWeights false) i k)
      (history .h2390 i) = _
    rw [register_eq false (i+1) (by omega),register_eq false i (by omega),history_eq i (by omega)]
    exact seed_charge_eq ⟨i,h⟩
  · decide +kernel

private abbrev count := laterCount Band.h2390+1
private def stepCost (i : ℕ) (k : Fin 4) : ℚ := registry true (i+1) k - registry true i k

private theorem step_nonneg (i : ℕ) (hi : i ∈ range count) (k : Fin 4) : 0 ≤ stepCost i k := by
  rw [stepCost, ← register_step true ⟨i,mem_range.mp hi⟩ k]
  exact sub_nonneg.mpr (le_max_left _ _)

private def prefersExit (i : ℕ) (k : Fin 4) (pivot : ℚ) : Prop :=
  i < stopIndex .h2390 ∨ rankReceipt k - pivot ≤ receipt i k

private instance (i : ℕ) (k : Fin 4) (pivot : ℚ) : Decidable (prefersExit i k pivot) := by
  unfold prefersExit
  infer_instance

private def intercept (k : Fin 4) (offset pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, stepCost i k * (if prefersExit i k pivot then
    (if i < stopIndex .h2390 then receipt i k else rankReceipt k) + offset else receipt i k)

private def gradient (k : Fin 4) (pivot : ℚ) : ℚ :=
  ∑ i ∈ range count, if prefersExit i k pivot then stepCost i k else 0

private theorem bound_coordinate (k : Fin 4) (offset pivot x : ℚ) (used : Mass)
    (hx : used k = x-offset) :
    (∑ i ∈ range count, stepCost i k *
      remainder (stopIndex .h2390) receipt rankReceipt used i k) ≤
      intercept k offset pivot - gradient k pivot * x := by
  unfold intercept gradient
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_le_sum
  intro i hi
  by_cases ht : i < stopIndex .h2390
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
    weightedBill count (lossWeight .h2390 rate0 rate1)
      (remainder (stopIndex .h2390) (history .h2390) (rankMass .h2390) used) =
      ∑ k : Fin 4, ∑ i ∈ range count, stepCost i k *
        remainder (stopIndex .h2390) receipt rankReceipt used i k := by
  unfold weightedBill
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i < count := mem_range.mp hi
  have h₀ := register_eq true i (by omega : i ≤ count)
  have h₁ := register_eq true (i+1) (by omega : i+1 ≤ count)
  change dotQ (fun k => running (tariffWeights true) (i+1) k - running (tariffWeights true) i k)
    (remainder (stopIndex .h2390) (history .h2390) (rankMass .h2390) used i) = _
  rw [h₀,h₁]
  unfold dotQ
  apply sum_congr rfl
  intro k _
  unfold stepCost remainder
  rw [history_eq i (Nat.le_of_lt_succ hi'),rank_eq]

private theorem seed_and_static : intercept 0 0 0 + intercept 3 0 0 + seedCredit = (14539691242097697722718147650700351458993/253075625913632967244800) := by
  decide +kernel

private theorem bill_and_fee {B J : ℕ} (pb pj cb cj mb mj : ℚ)
    (hb : intercept 2 2 pb = cb) (hb' : gradient 2 pb = mb)
    (hj : intercept 1 1 pj = cj) (hj' : gradient 1 pj = mj) :
    weightedBill count (lossWeight .h2390 rate0 rate1)
      (remainder (stopIndex .h2390) (history .h2390) (rankMass .h2390)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2390 +
      charge (lambdaDegree .h2390) (Peer653NativePrefixJointRank.mu .h2390) 0 0 0 B J ≤
      charge (lambdaDegree .h2390) (Peer653NativePrefixJointRank.mu .h2390) ((14539691242097697722718147650700351458993/253075625913632967244800) + cb + cj) mb mj B J := by
  let used : Mass := ![0,(J : ℚ)-1,(B : ℚ)-2,0]
  have h0 := bound_coordinate 0 0 0 0 used (by simp [used])
  have h1 := bound_coordinate 1 1 pj J used (by rfl)
  have h2 := bound_coordinate 2 2 pb B used (by rfl)
  have h3 := bound_coordinate 3 0 0 0 used (by simp [used])
  change weightedBill count (lossWeight .h2390 rate0 rate1)
    (remainder (stopIndex .h2390) (history .h2390) (rankMass .h2390) used) + seedLimit .h2390 + _ ≤ _
  rw [bill_by_coordinates,seed_exact,Fin.sum_univ_four]
  rw [hb,hb'] at h2
  rw [hj,hj'] at h1
  unfold charge
  linarith only [h0,h1,h2,h3,seed_and_static]

private theorem b0 : intercept 2 2 (958783/18) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (958783/18) = 41158786136 := by decide +kernel

private theorem b1 : intercept 2 2 (1213463/9) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (1213463/9) = 41158786136 := by decide +kernel

private theorem b2 : intercept 2 2 (5360317/32) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (5360317/32) = 41158786136 := by decide +kernel

private theorem b3 : intercept 2 2 (176237877/800) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (176237877/800) = 41158786136 := by decide +kernel

private theorem b4 : intercept 2 2 (106528829/350) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (106528829/350) = 41158786136 := by decide +kernel

private theorem b5 : intercept 2 2 (133473065/378) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (133473065/378) = 41158786136 := by decide +kernel

private theorem b6 : intercept 2 2 (1700525824/4563) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (1700525824/4563) = 41158786136 := by decide +kernel

private theorem b7 : intercept 2 2 (38213435593/97682) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (38213435593/97682) = 41158786136 := by decide +kernel

private theorem b8 : intercept 2 2 (159811433845/390728) = (2259748250364329156884842661/78780879450) ∧
    gradient 2 (159811433845/390728) = 41158786136 := by decide +kernel

private theorem b9 : intercept 2 2 (694731538577/1656200) = (17040325512637236789032569/466159050) ∧
    gradient 2 (694731538577/1656200) = 60133756304 := by decide +kernel

private theorem b10 : intercept 2 2 (60795763941/142100) = (24484016687053603705549/380538) ∧
    gradient 2 (60795763941/142100) = 125642697310 := by decide +kernel

private theorem b11 : intercept 2 2 (329258917015/761076) = (690913101919710613378/6561) ∧
    gradient 2 (329258917015/761076) = 220574219435 := by decide +kernel

private theorem b12 : intercept 2 2 (5972501947/13122) = 107164939221330320 ∧
    gradient 2 (5972501947/13122) = 224860075792 := by decide +kernel

private theorem j0 : intercept 1 1 (149405/18) = (659517799015422543591244444039909/21515645269131552) ∧
    gradient 1 (149405/18) = 180597715064 := by decide +kernel

private theorem j1 : intercept 1 1 (2058203/72) = (659517799015422543591244444039909/21515645269131552) ∧
    gradient 1 (2058203/72) = 180597715064 := by decide +kernel

private theorem j2 : intercept 1 1 (1898711/40) = (659517799015422543591244444039909/21515645269131552) ∧
    gradient 1 (1898711/40) = 180597715064 := by decide +kernel

private theorem j3 : intercept 1 1 (5427001/90) = (659517799015422543591244444039909/21515645269131552) ∧
    gradient 1 (5427001/90) = 180597715064 := by decide +kernel

private theorem j4 : intercept 1 1 (40496707/576) = (670992854268321832530150766947589/21515645269131552) ∧
    gradient 1 (40496707/576) = 188649613695 := by decide +kernel

private theorem j5 : intercept 1 1 (603226035/7744) = (22648960627287835975882747075283/672363914660361) ∧
    gradient 1 (603226035/7744) = 222252032616 := by decide +kernel

private theorem j6 : intercept 1 1 (2916513741/34969) = (26404965650121203078346073775027/672363914660361) ∧
    gradient 1 (2916513741/34969) = 290866334800 := by decide +kernel

private theorem j7 : intercept 1 1 (2437381245/28322) = (101211332117876797614631106387/2326518735849) ∧
    gradient 1 (2437381245/28322) = 340420085644 := by decide +kernel

private theorem j8 : intercept 1 1 (8731712015/100352) = (2939144976467961304507324325/47479974201) ∧
    gradient 1 (8731712015/100352) = 552569076538 := by decide +kernel

private theorem j9 : intercept 1 1 (172195907199/1968128) = (2939144976467961304507324325/47479974201) ∧
    gradient 1 (172195907199/1968128) = 552569076538 := by decide +kernel

private theorem j10 : intercept 1 1 (85231041/961) = (3369526792788098152249169/49406841) ∧
    gradient 1 (85231041/961) = 624374634504 := by decide +kernel

private theorem j11 : intercept 1 1 (1818151691/20164) = (4655682684399715146198689/49406841) ∧
    gradient 1 (1818151691/20164) = 914618133392 := by decide +kernel

private theorem j12 : intercept 1 1 (17956992355937/197627364) = (1256883271210232865554/9801) ∧
    gradient 1 (17956992355937/197627364) = 1289790402534 := by decide +kernel

private theorem j13 : intercept 1 1 (1847364601/19602) = 165672954831479160 ∧
    gradient 1 (1847364601/19602) = 1700779743676 := by decide +kernel

private theorem checked_bound (B J : ℕ) (hB₀ : 2 ≤ B) (hJ₀ : 1 ≤ J)
    (hB₁ : B ≤ capB .h2390) (hJ₁ : J ≤ capJ .h2390) :
    weightedBill count (lossWeight .h2390 rate0 rate1)
      (remainder (stopIndex .h2390) (history .h2390) (rankMass .h2390)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2390 +
      charge (lambdaDegree .h2390) (Peer653NativePrefixJointRank.mu .h2390) 0 0 0 B J ≤ (fees .h2390).loss := by
  have hL : 0 ≤ lambdaDegree .h2390 := by unfold lambdaDegree; positivity
  have hBmax : capB .h2390 = 476585 := by decide +kernel
  have groupsB : (2 ≤ B ∧ B ≤ 106533) ∨ (106534 ≤ B ∧ B ≤ 163129) ∨ (163129 ≤ B ∧ B ≤ 171894) ∨ (171895 ≤ B ∧ B ≤ 268703) ∨ (268704 ≤ B ∧ B ≤ 340036) ∨ (340037 ≤ B ∧ B ≤ 366174) ∨ (366175 ≤ B ∧ B ≤ 379183) ∨ (379184 ≤ B ∧ B ≤ 403224) ∨ (403225 ≤ B ∧ B ≤ 414797) ∨ (414798 ≤ B ∧ B ≤ 424152) ∨ (424153 ≤ B ∧ B ≤ 431527) ∨ (431528 ≤ B ∧ B ≤ 433722) ∨ (433723 ≤ B ∧ B ≤ 476585) := by omega
  have hJmax : capJ .h2390 = 97410 := by decide +kernel
  have groupsJ : (1 ≤ J ∧ J ≤ 16601) ∨ (16602 ≤ J ∧ J ≤ 40572) ∨ (40573 ≤ J ∧ J ≤ 54364) ∨ (54365 ≤ J ∧ J ≤ 66237) ∨ (66238 ≤ J ∧ J ≤ 74378) ∨ (74379 ≤ J ∧ J ≤ 81415) ∨ (81416 ≤ J ∧ J ≤ 85392) ∨ (85393 ≤ J ∧ J ≤ 86729) ∨ (86730 ≤ J ∧ J ≤ 87294) ∨ (87295 ≤ J ∧ J ≤ 87691) ∨ (87692 ≤ J ∧ J ≤ 89690) ∨ (89690 ≤ J ∧ J ≤ 90648) ∨ (90649 ≤ J ∧ J ≤ 91079) ∨ (91080 ≤ J ∧ J ≤ 97410) := by omega
  rcases groupsB with ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩
  all_goals rcases groupsJ with ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 1) (J₁ := 16601)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 16602) (P₁ := 16602) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 40573) (P₁ := 40573) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 54365) (P₁ := 54365) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 66238) (P₁ := 66238) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := 74379) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b0.1 b0.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 106533) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 1) (J₁ := 16601)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 16602) (P₁ := 16602) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 40573) (P₁ := 40573) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 54365) (P₁ := 54365) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 66238) (P₁ := 66238) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := 74379) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b1.1 b1.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 106534) (B₁ := 163129) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 1) (J₁ := 16601)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 16602) (P₁ := 16602) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 40573) (P₁ := 40573) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 54365) (P₁ := 54365) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 66238) (P₁ := 66238) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := 74379) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b2.1 b2.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 163129) (B₁ := 171894) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 1) (J₁ := 16601)
      (P₀ := 1) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 16602) (P₁ := (432198250039799145/11749764235264)) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 40573) (P₁ := 40573) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 54365) (P₁ := 54365) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 66238) (P₁ := 66238) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := 74379) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b3.1 b3.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 171895) (B₁ := 268703) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 16602) (J₁ := 40572)
      (P₀ := (432209999804034409/11749764235264)) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 40573) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 54365) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 66238) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := 74379) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b4.1 b4.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 268704) (B₁ := 340036) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 74379) (P₁ := (948946811185902585/11749764235264)) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b5.1 b5.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 340037) (B₁ := 366174) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 74379) (J₁ := 81415)
      (P₀ := (948958560950137849/11749764235264)) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b6.1 b6.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 366175) (B₁ := 379183) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b7.1 b7.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 379184) (B₁ := 403224) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b8.1 b8.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 403225) (B₁ := 414797) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b9.1 b9.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 414798) (B₁ := 424152) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b10.1 b10.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 424153) (B₁ := 431527) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 81416) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b11.1 b11.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 431528) (B₁ := 433722) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j0.1 j0.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 1) (J₁ := 16601)
      (P₀ := 16601) (P₁ := 16601) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j1.1 j1.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 16602) (J₁ := 40572)
      (P₀ := 40572) (P₁ := 40572) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j2.1 j2.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 40573) (J₁ := 54364)
      (P₀ := 54364) (P₁ := 54364) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j3.1 j3.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 54365) (J₁ := 66237)
      (P₀ := 66237) (P₁ := 66237) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j4.1 j4.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 66238) (J₁ := 74378)
      (P₀ := 74378) (P₁ := 74378) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j5.1 j5.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 74379) (J₁ := 81415)
      (P₀ := 81415) (P₁ := 81415) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j6.1 j6.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 81416) (J₁ := 85392)
      (P₀ := 81416) (P₁ := 85392) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j7.1 j7.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 85393) (J₁ := 86729)
      (P₀ := 85393) (P₁ := 85393) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j8.1 j8.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 86730) (J₁ := 87294)
      (P₀ := 86730) (P₁ := 86730) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j9.1 j9.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 87295) (J₁ := 87691)
      (P₀ := 87295) (P₁ := 87295) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j10.1 j10.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 87692) (J₁ := 89690)
      (P₀ := 87692) (P₁ := 87692) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j11.1 j11.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 89690) (J₁ := 90648)
      (P₀ := 89690) (P₁ := 89690) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j12.1 j12.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 90649) (J₁ := 91079)
      (P₀ := 90649) (P₁ := 90649) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (bill_and_fee _ _ _ _ _ _ b12.1 b12.2 j13.1 j13.2).trans ?_
    exact charge_over_range (B₀ := 433723) (B₁ := 476585) (J₀ := 91080) (J₁ := 97410)
      (P₀ := 91080) (P₁ := 91080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem loss_ledger (b : Band) : LossLedger b := by
  cases b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [seed_exact]; decide +kernel
  · decide +kernel
  · intro _
    refine ⟨rate0, rate1, ?_, checked_bound, ?_⟩
    · intro i hi
      refine ⟨rate_valid ⟨i,by omega⟩, ?_⟩
      rw [seed_exact,history_eq i hi]
      have H : ∀ i : Fin count,
          min seedCredit (dotQ (cutWeight .h2390 0 i) (receipt i)) ≤ rate0 i := by
        decide +kernel
      exact H ⟨i,Nat.lt_succ_of_le hi⟩
    · change (Peer653NativePrefix.terminalCredit : ℚ) ≤ running (tariffWeights true) count 0
      rw [register_eq true count le_rfl]
      decide +kernel
  · decide +kernel
  · intro hi
    exact ((by decide : ¬ 7773 ≤ start .h2390) hi).elim

#print axioms schedule
#print axioms loss_ledger
end Peer653NativePrefix
