import ProximityPrize.SubmissionLower.HighCore82229ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82229

open Finset
open HighCore82229_3
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

private def historyTable : Band → List Mass
  | .h2367 => [![7409, 96304, 470246, 2623776], ![(13335/2), 96304, 470246, 2623776], ![(34519/9), (232478/3), (1065137/3), 2272326], ![(8997/4), (215367/4), 315648, 1669392], ![(41833/25), (1015377/25), (4602817/16), 1476225], ![(13727/9), (536111/18), (4967146/25), (30479592/25)], ![(4029/4), (1398885/64), (268275/2), (6124992/7)], ![(90802/121), (1848107/121), (2847815/27), (62272451/81)], ![(126326/289), (3291274/289), (15598695/169), (62272451/81)], ![(126326/289), (3291274/289), (15598695/169), 502681], ![(126326/289), (4461970/441), (20094334/289), (25503394/81)], ![(142973/512), (74543/8), (43367772/625), (25503394/81)], ![(142973/512), (281320/31), (39027423/676), (22186904/81)], ![(142973/512), (13463802/1849), (60624358/1225), (22186904/81)], ![(142973/512), (64207569/10082), (35699607/841), (234211601/900)], ![(516397/2592), (64207569/10082), (35699607/841), (234211601/900)], ![(516397/2592), (58423037/9801), (88315019/2187), (1762398143/7056)]]
  | .h2395 => [![6465, 74788, 360972, 1879745], ![5001, 74788, 360972, 1879745], ![(24326/9), (482840/9), (2231366/9), (13837352/9)], ![(7177/4), (582283/16), (2231366/9), 1026169], ![(32959/25), (676474/25), (3105897/16), 1026169], ![(4651/4), (122423/6), 134988, 790117], ![(45508/49), (827322/49), 108621, 716526], ![(6640/11), (1293779/121), (5981113/81), (4017655/9)], ![(102974/289), (2269511/289), (10427241/169), (4017655/9)], ![(102974/289), (2734840/361), (1368586/25), (15262569/64)], ![(58697/192), (487277/72), (17873928/361), (15262569/64)], ![(71797/256), (741769/128), (26849048/625), (15262569/64)], ![(222162/1225), (741769/128), (26849048/625), (15262569/64)], ![(63671/400), (741769/128), (26849048/625), (15262569/64)], ![(63671/400), (45228047/8427), (6050240/169), (292058984/2025)], ![(63671/400), (44381107/10140), (121229629/3844), (292058984/2025)], ![(63671/400), (39541841/9216), (177190198/5929), (292058984/2025)], ![(63671/400), (17225263/4096), (10463674/363), (292058984/2025)]]
  | .h7773 => [![132, 1314, 7602, 34314], ![(175/3), (1238/3), (9707/2), 14938], ![(463/9), (3040/9), (24675/8), (142175/16)], ![(2131/50), (2943/10), (130842/49), (393579/49)]]

private def receipt (b : Band) (i : ℕ) : Mass :=
  (historyTable b)[i]?.getD (fun _ => 0)

private theorem receipt_zero (b : Band) : history b 0 = receipt b 0 := by
  funext k
  cases b <;> fin_cases k <;> decide +kernel

private theorem receipt_check (b : Band) :
    ∀ i : Fin (laterCount b), ∀ k : Fin 4,
      capMin (receipt b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1))) k =
        receipt b (i+1) k := by
  cases b <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_eq (b : Band) (i : ℕ) (hi : i ≤ laterCount b) :
    history b i = receipt b i := by
  induction i with
  | zero => exact receipt_zero b
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount b)]
    funext k
    exact receipt_check b ⟨i,by omega⟩ k

private theorem bill_eq (b : Band) (v : ℕ → Mass) :
    weightedBill (laterCount b+1) v (history b) =
    weightedBill (laterCount b+1) v (receipt b) := by
  unfold weightedBill
  apply sum_congr rfl
  intro i hi
  rw [history_eq b i (by simpa using hi)]

private def rate0Table : Band → List ℚ
  | .h2367 => [244876826, 252104030, 209371099, 193413264, 154984534, 146945208, 129133618, 111476825, 133169153, 98071243, 82059366, 79578997, 84512873, 114921748, 110303097, 151780259, 159596562]
  | .h2395 => [152325994, 144298632, 129134057, 120129633, 105630365, 96775117, 83230183, 68188580, 76096147, 64531381, 58375571, 46431484, 109532051, 74761629, 72489809, 77444654, 99248193, 134604256]
  | .h7773 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2367 => [1489428, 1434491, 1781174, 1948768, 2482517, 2616101, 3006383, 3524641, 2917958, 4033640, 4856786, 5011965, 4711185, 3405125, 3565362, 2535760, 2405882]
  | .h2395 => [2627620, 2780908, 3126461, 3388067, 3876367, 4251616, 4978531, 6120252, 5462160, 6477407, 7177517, 9081570, 3735597, 5557950, 5745608, 5365366, 4143135, 3001812]
  | .h7773 => []

private def rate1 (b : Band) (i : ℕ) : ℚ :=
  (rate1Table b)[i]?.getD 0

private abbrev Q : ℚ := ((p+1 : ℕ) : ℚ)
private def alpha (hi : ℕ) : ℚ := 1 + 2 * ((blockLength : ℚ) / agreement) * degreeAt hi
private def mu (hi : ℕ) : ℚ := ((blockLength - degreeAt hi : ℕ) : ℚ) / gap hi
private def drop (a : ℚ) := a / Q
private def quad (hi : ℕ) (a : ℚ) := 2 * alpha hi * drop a
private def slope (hi : ℕ) (a : ℚ) := 2 * alpha hi - (mu hi - alpha hi) * drop a
private def raw (hi : ℕ) (a : ℚ) (g : ℕ) :=
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
private def rateCheck (hi : ℕ) (a h : ℚ) (m : ℕ) : Bool :=
  decide (Q/81 ≤ a) && decide (0 ≤ h) && decide (0 ≤ quad hi a) &&
    (decide (m = 1) || decide (quad hi a * (2 * (m : ℚ) - 1) ≤ slope hi a)) &&
    decide (slope hi a ≤ quad hi a * (2 * (m : ℚ) + 1)) && decide (raw hi a m ≤ h)
private theorem rate_of_check {hi : ℕ} {a h : ℚ} {m : ℕ}
    (hc : rateCheck hi a h m = true) : RateOK hi a h := by
  simp only [rateCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨ha, hh⟩, hquad⟩, hl⟩, hr⟩, hp⟩
  refine ⟨ha, hh, fun g hg _ => ?_⟩
  by_cases hz : 0 ≤ 1 - a * g / Q
  · rw [max_eq_right hz]
    exact (raw_le_peak hi a g m hg hquad hl hr).trans hp
  · rw [max_eq_left (le_of_not_ge hz), zero_mul]
    exact hh

private def peakTable : Band → List ℕ
  | .h2367 => [5, 4, 5, 6, 7, 8, 9, 10, 8, 11, 13, 14, 13, 10, 10, 7, 7]
  | .h2395 => [7, 8, 8, 9, 10, 11, 13, 16, 14, 17, 18, 23, 10, 14, 15, 14, 11, 8]
  | .h7773 => []

private def peak (b : Band) (i : ℕ) : ℕ := (peakTable b)[i]?.getD 0

private theorem rates_check (b : Band) (hb : start b < 7773) :
    ∀ i : Fin (laterCount b+1), rateCheck (finish b) (rate0 b i) (rate1 b i) (peak b i) = true := by
  cases b <;> try (simp [start] at hb) <;> intro i <;> fin_cases i <;> decide +kernel

private theorem rate_valid (b : Band) (hb : start b < 7773) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i) :=
  rate_of_check (rates_check b hb i)


private def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeight b (rate0 b) (rate1 b) else cutWeight b 0

private def registerTable : Band → Bool → List Mass
  | .h2367, false => [![0, 0, 0, 0], ![18714, 478, 128, 0], ![19257, 557, 149, 0], ![23186, 557, 149, 0], ![25099, 577, 154, 0], ![25099, 704, 188, 0], ![27968, 751, 201, 0], ![31183, 948, 254, 0], ![43547, 1114, 298, 0], ![43547, 1114, 298, 0], ![46412, 1432, 383, 0], ![82316, 1606, 429, 0], ![82316, 1763, 472, 0], ![84839, 2478, 664, 0], ![129506, 3836, 1027, 0], ![202285, 3836, 1027, 0], ![202285, 5262, 1405, 0], ![373000, 5262, 1405, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![4582624921764, 144924278420, 31344233728, 190646784], ![4854767305710, 168045937897, 37563500470, 213739159], ![4854767305710, 168045937897, 37563500470, 256489056], ![4854767305710, 168045937897, 37563500470, 300110272], ![4854767305710, 168045937897, 37563500470, 466713196], ![4854767305710, 183522963976, 37563500470, 525836301], ![4854767305710, 216166710953, 37563500470, 763621282], ![4854767305710, 277672724677, 37563500470, 1050343018], ![4854767305710, 277672724677, 37563500470, 1050343018], ![4854767305710, 327647319656, 37563500470, 1544884120], ![6754798771656, 531578538172, 37563500470, 2083561194], ![6754798771656, 531578538172, 37563500470, 2365647480], ![7169987632447, 609115123509, 56116547672, 3128226840], ![14883055896488, 881823943578, 118024635196, 3497063375], ![22312661976645, 1056320060856, 118024635196, 3497063375], ![26714995166849, 1244989376218, 213251263895, 3562742800], ![59529517626000, 1706069765654, 217689710568, 3562742800]]
  | .h2395, false => [![0, 0, 0, 0], ![13538, 379, 101, 0], ![14444, 423, 112, 0], ![15887, 452, 120, 0], ![17350, 481, 128, 0], ![17350, 573, 153, 0], ![17692, 625, 167, 0], ![22445, 764, 204, 0], ![30754, 934, 249, 0], ![31997, 1045, 279, 0], ![40187, 1221, 329, 0], ![47176, 1604, 430, 0], ![83206, 1604, 430, 0], ![184205, 1604, 430, 0], ![184205, 2470, 661, 0], ![184205, 3811, 1019, 0], ![184205, 4575, 1223, 0], ![184205, 6023, 1607, 0], ![225000, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2062189306772, 93304271286, 15384925394, 265389620], ![2084249440608, 101205756488, 16161446784, 311461696], ![2084249440608, 108038679671, 16161446784, 375175320], ![2084249440608, 116565315923, 16161446784, 433672576], ![2084249440608, 125691804782, 16161446784, 593084151], ![2084249440608, 135704038397, 16161446784, 710019872], ![2084249440608, 175330988107, 16978957332, 1015620324], ![2097071589320, 251910363728, 16978957332, 1523942748], ![2434848415559, 254293207135, 21230825013, 1523942748], ![2593322608247, 339100371310, 21230825013, 2131066903], ![2753925937496, 432240957876, 25101495530, 3086332310], ![3863378057704, 817812870496, 25101495530, 3242120490], ![20176351454455, 837736427051, 39322006309, 3242120490], ![20176351454455, 837736427051, 49417436769, 3673804950], ![20176351454455, 837736712683, 73867115371, 5854774552], ![20176351454455, 989697395234, 94714811842, 6561842618], ![20176351454455, 1245331437534, 159491846151, 6658017945], ![30285957600000, 1791007773728, 298552239808, 6658019016]]
  | .h7773, false => [![0, 0, 0, 0], ![388, 44, 9, 0], ![605, 74, 15, 0], ![1017, 117, 24, 0], ![1017, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [244876826, (42207269/2), (135625151/9), (27831561/4), (2987820257/200), (3761380739/450), (937826505/64), (53757232690/3267), 0, (621226744293/48841), (877403907136/42483), (22233045443/5000), (49027663788569/2682368), (46765896269493327/1159692800), (10405431967/512), (106526506961463/4239481), (29385571285/864)]
  | .h2367, true => [63149170744302628, 7026392166899495, 97141702450422, 72820909020672, 245943401481900, (15991464288872407/30), (58980789533647749/64), (3789227983626048388/3267), 0, (236324449250612764/289), (3513938800112877884360/1147041), (2398052564618228/27), (5631824056705775727245/2682368), (15956777873001308620646207/2184537600), (8222933607897438520793/2580992), (16862155320343941501471149/2747183688), (80152303121882668721161/8468064)]
  | .h2395, false => [152325994, 11792270, (66955706/9), (815588947/144), (2936955353/400), (20090951/6), (528227155/49), (11060059475/1089), (154609375577/48841), (729123218008/104329), (2023095373775/207936), (1293422955/128), (22438139838/1225), (597677561257/40000), (9500916803801/474721), (23819369156222/2436135), (120817560636173/6830208), (250022831827537/7434240)]
  | .h2395, true => [26362485809788216, 1068165238292712, (4180836472163368/9), (1481341116949885/4), (10263412837057541/25), (593361694088429/2), (47864951940475560/49), (382411273105752757/363), (1153236310734926348/2873), (5633620598189139385803/6677056), (114250916789162856229/103968), (82647103670695127/32), (14444484528961643584899/3920000), (1073262813434401031/2000), (1143824127573114822138128/961310025), (937017673615185618236527/657756450), (9363915702684581597290007/3073593600), (441175342772681722265783/55756800)]
  | .h7773, false => [177450, (162478/3), (4570483/72), (6964164/245)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (105038701266219295400572736133630803/202660814473042313868480000)
  | .h2367, true => (689577384933631998370468601112822286143457/6544395736471665417945600)
  | .h2395, false => (46866700131619750329729703504703/132688938936492956160000)
  | .h2395, true => (523957978629917896856825480881691113509677/9752637011832232277760000)
  | .h7773, false => (5706776783/17640)
  | .h7773, true => 0

private def register (b : Band) (mode : Bool) (i : ℕ) : Mass :=
  (registerTable b mode)[i]?.getD (fun _ => 0)

private def charge (b : Band) (mode : Bool) (i : ℕ) : ℚ :=
  (chargeTable b mode)[i]?.getD 0

private theorem register_step (b : Band) (mode : Bool) :
    ∀ i : Fin (laterCount b+1), ∀ k : Fin 4,
      max (register b mode i k) (tariffWeights b mode i k) = register b mode (i+1) k := by
  cases b <;> cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (b : Band) (mode : Bool) (i : ℕ) (hi : i ≤ laterCount b+1) :
    running (tariffWeights b mode) i = register b mode i := by
  induction i with
  | zero => funext k; cases b <;> cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount b+1)]
    exact register_step b mode ⟨i,by omega⟩ k

private theorem charge_eq (b : Band) (mode : Bool) :
    ∀ i : Fin (laterCount b+1),
      dotQ (fun k => register b mode (i+1) k - register b mode i k) (receipt b i) =
        charge b mode i := by
  cases b <;> cases mode <;> intro i <;> fin_cases i <;> decide +kernel

private theorem bill_exact (b : Band) (mode : Bool) :
    weightedBill (laterCount b+1) (tariffWeights b mode) (receipt b) = credit b mode := by
  unfold weightedBill
  trans (∑ i ∈ range (laterCount b + 1), charge b mode i)
  · apply sum_congr rfl
    intro i hi
    have h : i < laterCount b + 1 := mem_range.mp hi
    simp only [register_eq b mode i (by omega : i ≤ laterCount b + 1),
      register_eq b mode (i+1) (by omega : i+1 ≤ laterCount b + 1)]
    exact charge_eq b mode ⟨i,h⟩
  · cases b <;> cases mode <;> decide +kernel


theorem loss_ledger (b : Band) : LossLedger b := by
  have seed : seedLimit b = credit b false :=
    (bill_eq b (tariffWeights b false)).trans (bill_exact b false)
  refine ⟨?_,?_,?_,?_⟩
  · rw [seed]
    cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · intro hb
    refine ⟨rate0 b,rate1 b,?_,?_⟩
    · intro i hi
      refine ⟨rate_valid b hb ⟨i,by omega⟩, ?_⟩
      rw [seed,history_eq b i hi]
      have H : ∀ i : Fin (laterCount b+1),
          min (credit b false) (dotQ (cutWeight b 0 i) (receipt b i)) ≤ rate0 b i := by
        cases b <;> try (simp [start] at hb) <;> decide +kernel
      exact H ⟨i,by omega⟩
    · have cost : weightedBill (laterCount b+1) (lossWeight b (rate0 b) (rate1 b)) (history b) =
          credit b true := (bill_eq b (tariffWeights b true)).trans (bill_exact b true)
      rw [cost,seed]
      cases b <;> try (simp [start] at hb) <;> decide +kernel
  · intro hb
    rw [seed]
    cases b <;> try (simp [start] at hb) <;> decide +kernel

#print axioms schedule
#print axioms loss_ledger
end HighCore82229
