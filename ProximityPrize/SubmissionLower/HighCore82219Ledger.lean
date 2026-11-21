import ProximityPrize.SubmissionLower.HighCore82219ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82219

open Finset
open HighCore82219_3
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
open HighCore82219JointRank (rankCharge rankRounding)

private def historyTable : List Mass := [![6436,78003,371788,2005662],
  ![4451,78003,371788,2005662],
  ![(35767/9),(556567/9),(2565578/9),(10769209/9)],
  ![2695,(172175/4),279188,(1561553/2)],
  ![(53983/36),(282907/12),(3877401/25),(16972452/25)],
  ![(67168/81),(1128305/81),(5245726/49),(1745041/4)],
  ![(57277/98),(926981/98),(768047/11),(2686321/9)],
  ![(147903/361),(2616811/361),(12164429/225),(2686321/9)],
  ![(147903/361),(2616811/361),(12164429/225),(22039686/121)],
  ![(205091/841),(2616811/361),(12164429/225),(22039686/121)],
  ![(205091/841),(5659172/961),(26015628/625),(22039686/121)],
  ![(205091/841),(2711415/529),(50035034/1369),(22039686/121)],
  ![(600622/3249),(2711415/529),(50035034/1369),(22039686/121)],
  ![(600622/3249),(17823389/3721),(1080039/32),(22039686/121)],
  ![(7646967/48223),(17823389/3721),(1080039/32),(22039686/121)],
  ![(106945/726),(17823389/3721),(1080039/32),(22039686/121)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)],
  ![(106945/726),(5537597/1250),(5161500/169),(100228375/588)]]

private def rankReceipt : Mass := ![6436,78003,371788,2005662]

private def receipt (i : ℕ) : Mass := historyTable[i]?.getD (fun _ => 0)

private theorem receipt_zero : history .h2405 0 = receipt 0 := by
  funext k
  fin_cases k <;> decide +kernel

private theorem receipt_check :
    ∀ i : Fin (laterCount .h2405), ∀ k : Fin 4,
      capMin (receipt i) (stageCap .h2405 (i+1) (decide (stopIndex .h2405 ≤ i+1))) k =
        receipt (i+1) k := by
  intro i k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (i : ℕ) (hi : i ≤ laterCount .h2405) :
    history .h2405 i = receipt i := by
  induction i with
  | zero => exact receipt_zero
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount .h2405)]
    funext k
    exact receipt_check ⟨i,by omega⟩ k

private theorem rank_eq : rankMass .h2405 = rankReceipt := by
  funext k
  fin_cases k <;> decide +kernel

private def rate0 (i : ℕ) : ℚ := ([160409623, 147903977, 134848447, 118600136, 97782420, 76410366, 63383026, 66233124, 57586661, 58375514, 65560190, 58535090, 59367130, 71076749, 91188263, 84265114, 493949777, 532676609, 193700585, 426141287, 710235478, 532676609, 193700585, 304386634, 177558870, 142047096, 106535322, 304386634, 133169153, 130071913] : List ℚ)[i]?.getD 0
private def rate1 (i : ℕ) : ℚ := ([2393798, 2601720, 2882879, 3302628, 4048234, 5233787, 6350025, 6065888, 7007270, 6905948, 6126870, 6887580, 6791808, 5640517, 4355398, 4728705, 626395, 583941, 1946465, 778587, 389294, 583941, 1946465, 1167880, 2141112, 2725050, 3698282, 1167880, 2919697, 2987603] : List ℚ)[i]?.getD 0
private def optimum (i : ℕ) : ℕ := ([7, 7, 8, 9, 11, 14, 17, 16, 19, 18, 17, 18, 18, 15, 12, 13, 2, 2, 6, 3, 2, 2, 6, 4, 6, 8, 10, 4, 8, 8] : List ℕ)[i]?.getD 0

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


private theorem rate_valid (i : Fin (laterCount .h2405+1)) : RateOK (finish .h2405) (rate0 i) (rate1 i) := by
  apply rate_of_check (m := optimum i)
  fin_cases i <;> decide +kernel

private def tariffCount (mode : Bool) := if mode then lossCount .h2405 else laterCount .h2405+1
private def tariffWeights (mode : Bool) : ℕ → Mass :=
  if mode then lossWeights .h2405 rate0 rate1 else cutWeight .h2405 0
private def tariffReceipt (mode : Bool) : ℕ → Mass :=
  if mode then splice (stopIndex .h2405) rankReceipt receipt else receipt
private def actualHistory (mode : Bool) : ℕ → Mass :=
  if mode then lossHistory .h2405 else history .h2405
private theorem actual_eq (mode : Bool) (i : ℕ) (hi : i < tariffCount mode) :
    actualHistory mode i = tariffReceipt mode i := by
  cases mode
  · exact history_eq i (by simpa [tariffCount] using Nat.le_of_lt_succ hi)
  · have hg : i < laterCount .h2405+2 := by simpa only [tariffCount, lossCount, jointRank, ite_true] using hi
    have ht : stopIndex .h2405 ≤ laterCount .h2405 := (schedule .h2405).stop_le
    change splice (stopIndex .h2405) (rankMass .h2405) (history .h2405) i = _
    rw [rank_eq]
    rcases lt_trichotomy i (stopIndex .h2405) with hlt | heq | hgt
    · simpa [splice, tariffReceipt, hlt] using history_eq i (by omega)
    · simp [splice, tariffReceipt, heq]
    · have hn : ¬ i < stopIndex .h2405 := by omega
      have hne : i ≠ stopIndex .h2405 := by omega
      simpa [splice, tariffReceipt, hn,hne] using history_eq (i-1) (by omega)

private def registerTable : Bool → List Mass
  | false => [![0,0,0,0],
    ![12714,445,118,0],
    ![13789,489,130,0],
    ![15124,521,138,0],
    ![17196,612,163,0],
    ![20857,717,191,0],
    ![26169,942,253,0],
    ![31892,1146,305,0],
    ![41506,1346,357,0],
    ![47738,1454,385,0],
    ![47738,1662,443,0],
    ![64726,2322,628,0],
    ![95409,2360,634,0],
    ![95409,2961,788,0],
    ![154657,3099,819,0],
    ![204112,3099,819,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![204112,4708,1261,0],
    ![219723,7729,2078,0]]
  | true => [![0,0,0,0],
    ![2039447946822,101817030007,18928335514,282468164],
    ![2039447946822,(503207694263206001173785407/3256080234375000),(1358702406447063492646/70283203125),282468164],
    ![2039447946822,(503207694263206001173785407/3256080234375000),(1358702406447063492646/70283203125),338223600],
    ![2039447946822,(503207694263206001173785407/3256080234375000),(1358702406447063492646/70283203125),397837302],
    ![2039447946822,(503207694263206001173785407/3256080234375000),(1358702406447063492646/70283203125),538328364],
    ![2039447946822,154544011678,(1358702406447063492646/70283203125),773212694],
    ![2039447946822,208941536775,19331822598,1324148111],
    ![2039447946822,275151945096,19331822930,1936757625],
    ![2749072044744,340920532232,23645225268,2165522016],
    ![2749072044744,418244060354,23645225268,2697798950],
    ![2749072044744,420991936844,25860352702,3059334964],
    ![4243448857940,548798548800,41171799320,3847674360],
    ![5584774401810,795279932620,41171799320,4366725720],
    ![5584774401810,795279932620,46781298440,5351944704],
    ![10992516770093,1092612282820,58211857431,5351944704],
    ![18612618737456,1092612387855,58211857431,5351944704],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![18612618737456,1092612387855,106258308754,5962897005],
    ![28579790940099,1661770909546,270289435214,6208239034]]

private def chargeTable : Bool → List ℚ
  | false => [160409623, 12678413, 9564857, (65922885/4), (2769276727/225), (56266622981/3969), (9599871857/1078), (666043530638/81225), (393936142232/81225), (377165569202/81225), (1589130013901936/101025125), (4809443217837439/609053041), (6307022287979/724201), (4897749403429169/386864928), (54025821855/6889), (1347005677715/59536), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1558030402400107/38341875)]
  | true => [28671784444206013, (2776052075276411197138594827793/651216046875000), 111826559278632, (213997472033906/3), 109692119669643, (6230675262223619010332235611851/39072962812500000), (371229040777678200173632249307/371938710937500), (7850231220801793459/9702), (86826258691643816447/81225), (28718237285798915346/43681), (2019996033785839147316/9828225), (116005618021725794859694884/61120200625), (90706120341217261994270/53831569), (63687601421784643536/165649), (1086972913299106713014593/386864928), (216825246951121647882286/179437783), (6709823290093992789/3872), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (22648268540533808761087929/2505002500)]

private def credit : Bool → ℚ
  | false => (3238203238867614827552169205535389709507983/8791940287548840515177406902580000)
  | true => (106657140671532774528651552336782621244116757201112319782896397/1908484199472868901261223120803828612812500000)

private def register (mode : Bool) (i : ℕ) : Mass :=
  (registerTable mode)[i]?.getD (fun _ => 0)

private def charge (mode : Bool) (i : ℕ) : ℚ :=
  (chargeTable mode)[i]?.getD 0

private theorem register_step (mode : Bool) :
    ∀ i : Fin (tariffCount mode), ∀ k : Fin 4,
      max (register mode i k) (tariffWeights mode i k) = register mode (i+1) k := by
  cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (mode : Bool) (i : ℕ) (hi : i ≤ tariffCount mode) :
    running (tariffWeights mode) i = register mode i := by
  induction i with
  | zero => funext k; cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ tariffCount mode)]
    exact register_step mode ⟨i,by omega⟩ k

private theorem charge_eq (mode : Bool) :
    ∀ i : Fin (tariffCount mode),
      dotQ (fun k => register mode (i+1) k - register mode i k) (tariffReceipt mode i) =
        charge mode i := by
  cases mode <;> intro i <;> fin_cases i <;> decide +kernel

private theorem bill_exact (mode : Bool) :
    weightedBill (tariffCount mode) (tariffWeights mode) (tariffReceipt mode) = credit mode := by
  unfold weightedBill
  trans (∑ i ∈ range (tariffCount mode), charge mode i)
  · apply sum_congr rfl
    intro i hi
    have h : i < tariffCount mode := mem_range.mp hi
    simp only [register_eq mode i (by omega : i ≤ tariffCount mode),
      register_eq mode (i+1) (by omega : i+1 ≤ tariffCount mode)]
    exact charge_eq mode ⟨i,h⟩
  · cases mode <;> decide +kernel


private theorem price (mode : Bool) :
    weightedBill (tariffCount mode) (tariffWeights mode) (actualHistory mode) = credit mode := by
  trans weightedBill (tariffCount mode) (tariffWeights mode) (tariffReceipt mode)
  · unfold weightedBill
    apply sum_congr rfl
    intro i hi
    rw [actual_eq mode i (mem_range.mp hi)]
  · exact bill_exact mode

theorem loss_ledger (b : Band) : LossLedger b := by
  cases b
  have seed : seedLimit .h2405 = credit false := price false
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [seed]
    decide +kernel
  · decide +kernel
  · intro _
    refine ⟨rate0,rate1,?_,?_⟩
    · intro i hi
      refine ⟨rate_valid ⟨i,by omega⟩, ?_⟩
      rw [seed, history_eq i hi]
      have H : ∀ i : Fin (laterCount .h2405+1),
          min (credit false) (dotQ (cutWeight .h2405 0 i) (receipt i)) ≤ rate0 i := by
        intro i
        fin_cases i <;> decide +kernel
      exact H ⟨i,by omega⟩
    · have charge : weightedBill (lossCount .h2405) (lossWeights .h2405 rate0 rate1)
          (lossHistory .h2405) = credit true := price true
      rw [charge,seed]
      decide +kernel
  · intro _
    decide +kernel
  · intro h
    have impossible : ¬ 7773 ≤ start .h2405 := by decide
    exact (impossible h).elim

#print axioms schedule
#print axioms loss_ledger
end HighCore82219
