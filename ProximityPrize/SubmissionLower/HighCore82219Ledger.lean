import ProximityPrize.SubmissionLower.HighCore82219ScheduleData
import ProximityPrize.SubmissionLower.HighCore82219PrefixGeometry -- serialize candidate build

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

theorem guard_of_fits {h r : ℕ} {s : Shape} (hf : Fits h r s) :
    BankGuard h r s :=
  ⟨⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.2.2.2.2.2.2⟩

theorem checked_fits (b : Band) :
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

def historyTable : Band → List Mass
  | .h2367 => [![7409, 97804, 478649, 2719980], ![(13335/2), 97804, 478649, 2719980], ![(34519/9), (732241/9), (3353014/9), 2404116], ![(8997/4), (457005/8), 313730, (28591795/16)], ![(41833/25), (1085546/25), (4917353/16), 1466521], ![(13727/9), (1129351/36), (1045977/5), (32538442/25)], ![(4029/4), (371397/16), (963274/7), (46305324/49)], ![(90802/121), (1947573/121), (8999483/81), (67086658/81)], ![(126326/289), (3498524/289), (16581034/169), (67086658/81)], ![(126326/289), (3498524/289), (16581034/169), (12851112/25)], ![(126326/289), (525536/49), (1252258/17), (9201530/27)], ![(142973/512), (10424567/1024), (1252258/17), (9201530/27)], ![(142973/512), (9400896/961), (42042493/676), (24502606/81)], ![(142973/512), (14313072/1849), (64400944/1225), (24502606/81)], ![(142973/512), (34176171/5041), (151977825/3364), (13645636/49)], ![(516397/2592), (34176171/5041), (151977825/3364), (13645636/49)], ![(516397/2592), (62015413/9801), (93685283/2187), (385088827/1445)]]
  | .h2395 => [![6465, 71862, 347161, 1759163], ![5001, 71862, 347161, 1759163], ![(24326/9), (464660/9), (2147195/9), (4248650/3)], ![(7177/4), (561707/16), (2147195/9), 946729], ![(32959/25), (130781/5), (3002199/16), 946729], ![(4651/4), 19884, (3288384/25), (18636156/25)], ![(45508/49), (805484/49), 104002, (6053056/9)], ![(6640/11), (1268216/121), (5862496/81), (1279712/3)], ![(102974/289), (2217722/289), (10186770/169), (1279712/3)], ![(102974/289), (2698866/361), (12155248/225), (7429195/32)], ![(58697/192), (1915661/288), (17564180/361), (7429195/32)], ![(71797/256), (2927007/512), (26479526/625), (7429195/32)], ![(222162/1225), (2927007/512), (26479526/625), (7429195/32)], ![(63671/400), (2927007/512), (26479526/625), (7429195/32)], ![(63671/400), (45002332/8427), (463240/13), (57844904/405)], ![(63671/400), (33165731/7605), (30197284/961), (57844904/405)], ![(63671/400), (39426043/9216), (176671466/5929), (57844904/405)], ![(63671/400), (68749093/16384), (10437700/363), (57844904/405)]]
  | .h7773 => [![132, 1256, 7256, 31232], ![(175/3), (1217/3), (19081/4), (28841/2)], ![(463/9), (3017/9), (6123/2), (140033/16)], ![(2131/50), (7337/25), (130476/49), (391404/49)]]

def receipt (b : Band) (i : ℕ) : Mass :=
  (historyTable b)[i]?.getD (fun _ => 0)

theorem receipt_zero (b : Band) : history b 0 = receipt b 0 := by
  funext k
  cases b <;> fin_cases k <;> decide +kernel

theorem receipt_check (b : Band) :
    ∀ i : Fin (laterCount b), ∀ k : Fin 4,
      capMin (receipt b i) (stageCap b (i+1) (decide (stopIndex b ≤ i+1))) k =
        receipt b (i+1) k := by
  cases b <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

theorem history_eq (b : Band) (i : ℕ) (hi : i ≤ laterCount b) :
    history b i = receipt b i := by
  induction i with
  | zero => exact receipt_zero b
  | succ i ih =>
    rw [history, ih (by omega : i ≤ laterCount b)]
    funext k
    exact receipt_check b ⟨i,by omega⟩ k

theorem bill_eq (b : Band) (v : ℕ → Mass) :
    weightedBill (laterCount b+1) v (history b) =
    weightedBill (laterCount b+1) v (receipt b) := by
  unfold weightedBill
  apply sum_congr rfl
  intro i hi
  rw [history_eq b i (by simpa using hi)]

def rate0Table : Band → List ℚ
  | .h2367 => [256686378, 262799320, 216250868, 198208795, 164190460, 146945236, 129133696, 113938482, 168056217, 102237856, 89072662, 82959955, 91086711, 122682772, 123314832, 144549924, 159288347]
  | .h2395 => [155241934, 146873295, 133169153, 118372580, 106535322, 96850293, 81950248, 68732466, 76096659, 64566862, 60877327, 46768174, 112142444, 73472636, 72544277, 77435132, 101462212, 135401388]
  | .h7773 => []

def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

def rate1Table : Band → List ℚ
  | .h2367 => [1411758, 1380489, 1725495, 1891908, 2330697, 2617391, 3007864, 3440934, 2266431, 3859796, 4461623, 4805711, 4360071, 3188175, 3170508, 2669902, 2412193]
  | .h2395 => [2579505, 2724640, 3037190, 3442149, 3847107, 4252066, 5061982, 6074378, 5466941, 6479337, 6884295, 9023348, 3644628, 5669420, 5746172, 5370782, 4049586, 2986280]
  | .h7773 => []

def rate1 (b : Band) (i : ℕ) : ℚ :=
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

def peakTable : Band → List ℕ
  | .h2367 => [4, 4, 5, 6, 7, 7, 8, 10, 7, 11, 12, 13, 12, 9, 9, 8, 7]
  | .h2395 => [7, 8, 8, 9, 10, 11, 13, 16, 14, 17, 18, 23, 10, 15, 15, 14, 11, 8]
  | .h7773 => []

private def peak (b : Band) (i : ℕ) : ℕ := (peakTable b)[i]?.getD 0

theorem rates_check (b : Band) (hb : start b < 7880) :
    ∀ i : Fin (laterCount b+1), rateCheck (finish b) (rate0 b i) (rate1 b i) (peak b i) = true := by
  cases b <;> try (simp [start] at hb) <;> intro i <;> fin_cases i <;> decide +kernel

theorem rate_valid (b : Band) (hb : start b < 7880) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i) :=
  rate_of_check (rates_check b hb i)


def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeight b (rate0 b) (rate1 b) else cutWeight b 0

def registerTable : Band → Bool → List Mass
  | .h2367, false => [![0, 0, 0, 0], ![20066, 478, 128, 0], ![20548, 557, 149, 0], ![24971, 557, 149, 0], ![27244, 577, 154, 0], ![27244, 704, 188, 0], ![30186, 751, 201, 0], ![33443, 948, 254, 0], ![47394, 1114, 298, 0], ![47394, 1114, 298, 0], ![49738, 1432, 383, 0], ![92074, 1606, 429, 0], ![92074, 1763, 472, 0], ![92074, 2478, 664, 0], ![139651, 3836, 1027, 0], ![236474, 3836, 1027, 0], ![236474, 5262, 1405, 0], ![375000, 5262, 1405, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![5150668860948, 151024424712, 32855856384, 180705024], ![5400000427360, 174745509212, 39157098680, 205692861], ![5400000427360, 174745509212, 39157098680, 248471280], ![5400000427360, 174745509212, 39157098680, 291353832], ![5400000427360, 174745509212, 39157098680, 438171036], ![5400000427360, 189364436962, 39157098680, 526095591], ![5400000427360, 223010739560, 39157098680, 763997456], ![5400000427360, 290007094944, 39157098680, 1025398332], ![6058090510416, 290007094944, 39157098680, 1025398332], ![6058090510416, 338383143240, 39157098848, 1478301868], ![8201276280988, 553850171274, 39157098848, 1914036267], ![8201276280988, 553850171274, 39157098848, 2268295592], ![8334069709656, 624641926074, 60481576104, 2895087144], ![17132771792572, 915842940317, 125995206844, 3274255725], ![29160751582368, 1124373168408, 125995206844, 3274255725], ![29160751582368, 1266351867026, 203092643220, 3751212310], ![59733130125000, 1658802698045, 203092643220, 3751212310]]
  | .h2395, false => [![0, 0, 0, 0], ![12990, 379, 101, 0], ![13930, 423, 112, 0], ![15343, 452, 120, 0], ![16783, 481, 128, 0], ![16783, 573, 153, 0], ![17344, 625, 167, 0], ![22064, 764, 204, 0], ![30271, 934, 249, 0], ![31580, 1045, 279, 0], ![39745, 1221, 329, 0], ![46807, 1604, 430, 0], ![81482, 1604, 430, 0], ![174982, 1604, 430, 0], ![174982, 2470, 661, 0], ![174982, 3811, 1019, 0], ![174982, 4575, 1223, 0], ![174982, 6023, 1607, 0], ![225000, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2016592722660, 92344462936, 15679435334, 260530005], ![2045944999350, 100081638985, 16449809040, 305159680], ![2045944999350, 106792063326, 16449809040, 364462800], ![2045944999350, 114706797647, 16449809040, 440595072], ![2045944999350, 124268095944, 16449809040, 588607371], ![2045944999350, 134279265829, 16449809040, 710095022], ![2045944999350, 174297560320, 16717850592, 1032644328], ![2080600478286, 248073619682, 17114384034, 1512520122], ![2403132491220, 252167005435, 21230967861, 1525276539], ![2566209930190, 336357387567, 21242497598, 2131701873], ![2849485044889, 419880428573, 26177250610, 2960246850], ![3810764353868, 797863026722, 26177250610, 3221335236], ![19622909136008, 797863026722, 40259137396, 3221335236], ![19622909136008, 797863026722, 48565412396, 3747486620], ![19622909136008, 836327269951, 73922618263, 5855349268], ![19622909136008, 988683981868, 94703166436, 6568466386], ![19622909136008, 1242708682538, 163049774684, 6568466386], ![30465312300000, 1794119703744, 300320278584, 6623569040]]
  | .h7773, false => [![0, 0, 0, 0], ![382, 44, 9, 0], ![601, 74, 15, 0], ![1014, 117, 24, 0], ![1014, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [256686378, 20991880, (152677537/9), (31294831/4), (3192789761/200), (173623489/20), (1696441499/112), (176709388912/9801), 0, (645373053354/48841), (336469864604/14161), (82962593579/17408), (3075293385264/162409), (49729433610203061/1159692800), (13843074779/512), (226769360571897/8478962), (35767205411/1296)]
  | .h2367, true => [69150035278820916, 7066484908111374, 102844281572604, (153261141982605/2), 215310512827284, (51574092603151541/90), (394284311738974527/392), (12690821571849526960/9801), (83133887832132256/289), (999329115742103158512/1221025), (1298544585857736479998/382347), (3259727806767250/27), (3780990386661921906376859/1683856512), (12947487116308719120022123/1565585280), (3079448011681714549765/645248), (135872487899076636172216/29676367), (112045901825274659687/13068)]
  | .h2395, false => [146279309, 11681639, (65025338/9), (793502167/144), (567784507/80), (352776579/100), (515315662/49), (10882134080/1089), (152701554152/48841), (6503468843990/938961), (250058379391/25992), (2489560975/256), (830885880/49), (2358014518911/160000), (727352886532/36517), (71199082706404/7308405), (120463821690895/6830208), (5209116014643911/148684800)]
  | .h2395, true => [25574932942676321, 1048754260070619, (3873940376653060/9), (5598987747058555/16), (1951073831679812/5), (7240615365943056/25), (56866942716950332/63), (3357090690172707280/3267), (19531973252198565956/48841), (311334171411487717954289/375584400), (223451466636978898931/207936), (1275426476263108889/512), (15156092200558985052/4375), (1896265992791145/4), (20853671622504232402204/14789385), (31117775891808190789937/21925215), (85331145463829025472589/27320832), (16047107808328943531467319/2007244800)]
  | .h7773, false => [170992, (107133/2), (1137863/18), (34723512/1225)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (32883534957681137707772760810103865/60311858387177392607259648)
  | .h2367, true => (63637665906847291455277895135594132353979701/565423672379788055693059200)
  | .h2395, false => (8979067270422950644398408738493381/26007032031552619407360000)
  | .h2395, true => (186875331709810326446949384573403725586439/3546413458848084464640000)
  | .h7773, false => (3485210158/11025)
  | .h7773, true => 0

def register (b : Band) (mode : Bool) (i : ℕ) : Mass :=
  (registerTable b mode)[i]?.getD (fun _ => 0)

private def charge (b : Band) (mode : Bool) (i : ℕ) : ℚ :=
  (chargeTable b mode)[i]?.getD 0

theorem register_step (b : Band) (mode : Bool) :
    ∀ i : Fin (laterCount b+1), ∀ k : Fin 4,
      max (register b mode i k) (tariffWeights b mode i k) = register b mode (i+1) k := by
  cases b <;> cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

theorem register_eq (b : Band) (mode : Bool) (i : ℕ) (hi : i ≤ laterCount b+1) :
    running (tariffWeights b mode) i = register b mode i := by
  induction i with
  | zero => funext k; cases b <;> cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ laterCount b+1)]
    exact register_step b mode ⟨i,by omega⟩ k

theorem charge_eq (b : Band) (mode : Bool) :
    ∀ i : Fin (laterCount b+1),
      dotQ (fun k => register b mode (i+1) k - register b mode i k) (receipt b i) =
        charge b mode i := by
  cases b <;> cases mode <;> intro i <;> fin_cases i <;> decide +kernel

theorem bill_exact (b : Band) (mode : Bool) :
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


open High50Nonlinear (remainder charge_over_range)

def jointRankReceipt : Mass := ![7409, 97804, 478649, 2719980]

theorem joint_rank_eq : rankMass .h2367 = jointRankReceipt := by
  change history .h2367 0 = _
  exact (history_eq .h2367 0 (Nat.zero_le _)).trans (by rfl)

abbrev jointCount := laterCount Band.h2367+1
def jointStepCost (i : ℕ) (k : Fin 4) : ℚ := register .h2367 true (i+1) k - register .h2367 true i k

theorem jointStep_nonneg (i : ℕ) (hi : i ∈ range jointCount) (k : Fin 4) : 0 ≤ jointStepCost i k := by
  rw [jointStepCost, ← register_step .h2367 true ⟨i,mem_range.mp hi⟩ k]
  exact sub_nonneg.mpr (le_max_left _ _)

def jointPrefersExit (i : ℕ) (k : Fin 4) (pivot : ℚ) : Prop :=
  i < stopIndex .h2367 ∨ jointRankReceipt k - pivot ≤ receipt .h2367 i k

private instance (i : ℕ) (k : Fin 4) (pivot : ℚ) : Decidable (jointPrefersExit i k pivot) := by
  unfold jointPrefersExit
  infer_instance

def jointIntercept (k : Fin 4) (offset pivot : ℚ) : ℚ :=
  ∑ i ∈ range jointCount, jointStepCost i k * (if jointPrefersExit i k pivot then
    (if i < stopIndex .h2367 then receipt .h2367 i k else jointRankReceipt k) + offset else receipt .h2367 i k)

def jointGradient (k : Fin 4) (pivot : ℚ) : ℚ :=
  ∑ i ∈ range jointCount, if jointPrefersExit i k pivot then jointStepCost i k else 0

theorem jointBound_coordinate (k : Fin 4) (offset pivot x : ℚ) (used : Mass)
    (hx : used k = x-offset) :
    (∑ i ∈ range jointCount, jointStepCost i k *
      remainder (stopIndex .h2367) (receipt .h2367) jointRankReceipt used i k) ≤
      jointIntercept k offset pivot - jointGradient k pivot * x := by
  unfold jointIntercept jointGradient
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_le_sum
  intro i hi
  by_cases ht : i < stopIndex .h2367
  · have hs : jointPrefersExit i k pivot := Or.inl ht
    simp only [remainder, ite_eq_left ht, ite_eq_left hs, hx]
    ring_nf
    exact le_rfl
  · simp only [remainder, ite_eq_right ht, hx]
    by_cases hs : jointPrefersExit i k pivot
    · simp only [ite_eq_left hs]
      have h := mul_le_mul_of_nonneg_left (min_le_right (receipt .h2367 i k) (jointRankReceipt k-(x-offset)))
        (jointStep_nonneg i hi k)
      convert h using 1
      ring
    · simp only [ite_eq_right hs, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (jointStep_nonneg i hi k)

theorem jointBill_by_coordinates (used : Mass) :
    weightedBill jointCount (lossWeight .h2367 (rate0 .h2367) (rate1 .h2367))
      (remainder (stopIndex .h2367) (history .h2367) (rankMass .h2367) used) =
      ∑ k : Fin 4, ∑ i ∈ range jointCount, jointStepCost i k *
        remainder (stopIndex .h2367) (receipt .h2367) jointRankReceipt used i k := by
  unfold weightedBill
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hi' : i < jointCount := mem_range.mp hi
  have h₀ := register_eq .h2367 true i (by omega : i ≤ jointCount)
  have h₁ := register_eq .h2367 true (i+1) (by omega : i+1 ≤ jointCount)
  change dotQ (fun k => running (tariffWeights .h2367 true) (i+1) k - running (tariffWeights .h2367 true) i k)
    (remainder (stopIndex .h2367) (history .h2367) (rankMass .h2367) used i) = _
  rw [h₀,h₁]
  unfold dotQ
  apply sum_congr rfl
  intro k _
  unfold jointStepCost remainder
  rw [history_eq .h2367 i (Nat.le_of_lt_succ hi'),joint_rank_eq]


theorem joint_seed_eq : seedLimit .h2367 = credit .h2367 false :=
  (bill_eq .h2367 (tariffWeights .h2367 false)).trans (bill_exact .h2367 false)

theorem joint_bill_and_fee {B J : ℕ} (pb pj cb cj mb mj : ℚ)
    (hb : jointIntercept 2 2 pb = cb) (hb' : jointGradient 2 pb = mb)
    (hj : jointIntercept 1 1 pj = cj) (hj' : jointGradient 1 pj = mj) :
    weightedBill jointCount (lossWeight .h2367 (rate0 .h2367) (rate1 .h2367))
      (remainder (stopIndex .h2367) (history .h2367) (rankMass .h2367)
        ![0,(J : ℚ)-1,(B : ℚ)-2,0]) + seedLimit .h2367 +
      High50Nonlinear.charge (jointL .h2367) (jointMu .h2367) 0 0 0 B J ≤
      High50Nonlinear.charge (jointL .h2367) (jointMu .h2367) ((jointIntercept 0 0 0 + jointIntercept 3 0 0 + credit .h2367 false) + cb + cj) mb mj B J := by
  let used : Mass := ![0,(J : ℚ)-1,(B : ℚ)-2,0]
  have h0 := jointBound_coordinate 0 0 0 0 used (by simp [used])
  have h1 := jointBound_coordinate 1 1 pj J used (by rfl)
  have h2 := jointBound_coordinate 2 2 pb B used (by rfl)
  have h3 := jointBound_coordinate 3 0 0 0 used (by simp [used])
  change weightedBill jointCount (lossWeight .h2367 (rate0 .h2367) (rate1 .h2367))
    (remainder (stopIndex .h2367) (history .h2367) (rankMass .h2367) used) + seedLimit .h2367 + _ ≤ _
  rw [jointBill_by_coordinates,joint_seed_eq,Fin.sum_univ_four]
  rw [hb,hb'] at h2
  rw [hj,hj'] at h1
  unfold High50Nonlinear.charge
  linarith only [h0,h1,h2,h3]


theorem jointBCell0 : jointIntercept 2 2 0 = (940047528038404985559128/34821605) ∧
    jointGradient 2 0 = 39157098680 := by decide +kernel

theorem jointBCell1 : jointIntercept 2 2 (380537/2) = (940047528038404985559128/34821605) ∧
    jointGradient 2 (380537/2) = 39157098680 := by decide +kernel

theorem jointBCell2 : jointIntercept 2 2 398496 = (940047530264565745485728/34821605) ∧
    jointGradient 2 398496 = 39157098848 := by decide +kernel

theorem jointBCell3 : jointIntercept 2 2 421266 = (7392245217613180217222/206045) ∧
    jointGradient 2 421266 = 60481576104 := by decide +kernel

theorem jointBCell4 : jointIntercept 2 2 429774 = (53648077576039630954/841) ∧
    jointGradient 2 429774 = 125995206844 := by decide +kernel

theorem jointBCell5 : jointIntercept 2 2 (912121/2) = 97210496769896220 ∧
    jointGradient 2 (912121/2) = 203092643220 := by decide +kernel

theorem jointJCell0 : jointIntercept 1 1 0 = (33275504917050676879027860634682555/1105067447295117768) ∧
    jointGradient 1 0 = 174745509212 := by decide +kernel

theorem jointJCell1 : jointIntercept 1 1 33217 = (33275504917050676879027860634682555/1105067447295117768) ∧
    jointGradient 1 33217 = 174745509212 := by decide +kernel

theorem jointJCell2 : jointIntercept 1 1 (141025/2) = (34348741865173475513766507169788055/1105067447295117768) ∧
    jointGradient 1 (141025/2) = 189364436962 := by decide +kernel

theorem jointJCell3 : jointIntercept 1 1 78150 = (4640275616458380208919091421258214/138133430911889721) ∧
    jointGradient 1 78150 = 223010739560 := by decide +kernel

theorem jointJCell4 : jointIntercept 1 1 (167407/2) = (5396449651302861778190284145830502/138133430911889721) ∧
    jointGradient 1 (167407/2) = 290007094944 := by decide +kernel

theorem jointJCell5 : jointIntercept 1 1 (172777/2) = (20654404383072742419397829838734/477970349176089) ∧
    jointGradient 1 (172777/2) = 338383143240 := by decide +kernel

theorem jointJCell6 : jointIntercept 1 1 87550 = (604540330939402404532066808600/9754496921961) ∧
    jointGradient 1 87550 = 553850171274 := by decide +kernel

theorem jointJCell7 : jointIntercept 1 1 (178085/2) = (692323902369506304754113800/10150361001) ∧
    jointGradient 1 (178085/2) = 624641926074 := by decide +kernel

theorem jointJCell8 : jointIntercept 1 1 90544 = (518407095771934542698639/5489649) ∧
    jointGradient 1 90544 = 915842940317 := by decide +kernel

theorem jointJCell9 : jointIntercept 1 1 (182501/2) = (137582910065119409753/1089) ∧
    jointGradient 1 (182501/2) = 1266351867026 := by decide +kernel

theorem jointJCell10 : jointIntercept 1 1 (189281/2) = 162239197882291225 ∧
    jointGradient 1 (189281/2) = 1658802698045 := by decide +kernel

theorem joint_receipt : JointBill .h2367 (lossWeight .h2367 (rate0 .h2367) (rate1 .h2367)) := by
  intro B J hB₀ hJ₀ hB₁ hJ₁
  have hL : 0 ≤ jointL .h2367 := by decide +kernel
  have hBmax : jointB .h2367 = 478651 := by decide +kernel
  have hJmax : jointJ .h2367 = 97805 := by decide +kernel
  have groupsB : (2 ≤ B ∧ B ≤ 2) ∨ (3 ≤ B ∧ B ≤ 380538) ∨ (380539 ≤ B ∧ B ≤ 416457) ∨ (416458 ≤ B ∧ B ≤ 426078) ∨ (426079 ≤ B ∧ B ≤ 433473) ∨ (433474 ≤ B ∧ B ≤ 478651) := by omega
  have groupsJ : (1 ≤ J ∧ J ≤ 1) ∨ (2 ≤ J ∧ J ≤ 66434) ∨ (66435 ≤ J ∧ J ≤ 74592) ∨ (74593 ≤ J ∧ J ≤ 81709) ∨ (81710 ≤ J ∧ J ≤ 85699) ∨ (85700 ≤ J ∧ J ≤ 87079) ∨ (87080 ≤ J ∧ J ≤ 88022) ∨ (88023 ≤ J ∧ J ≤ 90064) ∨ (90065 ≤ J ∧ J ≤ 91025) ∨ (91026 ≤ J ∧ J ≤ 91477) ∨ (91478 ≤ J ∧ J ≤ 97805) := by omega
  rcases groupsB with ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩ | ⟨hBlo, hBhi⟩
  all_goals rcases groupsJ with ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩ | ⟨hJlo, hJhi⟩
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 2) (J₁ := 66434)
      (P₀ := 2) (P₁ := 2) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 66435) (P₁ := 66435) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 74593) (P₁ := 74593) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 81710) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell0.1 jointBCell0.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 2) (B₁ := 2) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 2) (J₁ := 66434)
      (P₀ := 2) (P₁ := 66434) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 66435) (P₁ := 74592) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 74593) (P₁ := 81709) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 81710) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell1.1 jointBCell1.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 3) (B₁ := 380538) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 2) (J₁ := 66434)
      (P₀ := 66434) (P₁ := 66434) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 74592) (P₁ := 74592) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 81709) (P₁ := 81709) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 81710) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell2.1 jointBCell2.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 380539) (B₁ := 416457) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 2) (J₁ := 66434)
      (P₀ := 66434) (P₁ := 66434) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 74592) (P₁ := 74592) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 81709) (P₁ := 81709) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 81710) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell3.1 jointBCell3.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 416458) (B₁ := 426078) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 2) (J₁ := 66434)
      (P₀ := 66434) (P₁ := 66434) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 74592) (P₁ := 74592) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 81709) (P₁ := 81709) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 81710) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell4.1 jointBCell4.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 426079) (B₁ := 433473) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell0.1 jointJCell0.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 1) (J₁ := 1)
      (P₀ := 1) (P₁ := 1) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell1.1 jointJCell1.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 2) (J₁ := 66434)
      (P₀ := 66434) (P₁ := 66434) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell2.1 jointJCell2.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 66435) (J₁ := 74592)
      (P₀ := 74592) (P₁ := 74592) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell3.1 jointJCell3.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 74593) (J₁ := 81709)
      (P₀ := 81709) (P₁ := 81709) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell4.1 jointJCell4.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 81710) (J₁ := 85699)
      (P₀ := 81710) (P₁ := 85699) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell5.1 jointJCell5.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 85700) (J₁ := 87079)
      (P₀ := 85700) (P₁ := 85700) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell6.1 jointJCell6.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 87080) (J₁ := 88022)
      (P₀ := 87080) (P₁ := 87080) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell7.1 jointJCell7.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 88023) (J₁ := 90064)
      (P₀ := 88023) (P₁ := 88023) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell8.1 jointJCell8.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 90065) (J₁ := 91025)
      (P₀ := 90065) (P₁ := 90065) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell9.1 jointJCell9.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 91026) (J₁ := 91477)
      (P₀ := 91026) (P₁ := 91026) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · refine (joint_bill_and_fee _ _ _ _ _ _ jointBCell5.1 jointBCell5.2 jointJCell10.1 jointJCell10.2).trans ?_
    exact charge_over_range (B₀ := 433474) (B₁ := 478651) (J₀ := 91478) (J₁ := 97805)
      (P₀ := 91478) (P₁ := 91478) hL
      (by exact_mod_cast hBlo) (by exact_mod_cast hBhi) (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
    · by_cases hj : b = .h2367
      · subst b
        exact joint_receipt
      · rw [if_neg hj]
        have cost : weightedBill (laterCount b+1) (lossWeight b (rate0 b) (rate1 b)) (history b) =
            credit b true := (bill_eq b (tariffWeights b true)).trans (bill_exact b true)
        rw [cost,seed]
        cases b with
        | h2367 => exact (hj rfl).elim
        | h2395 => decide +kernel
        | h7773 => exact ((by decide : ¬ start Band.h7773 < 7880) hb).elim
  · intro hb
    rw [seed]
    cases b <;> try (simp [start] at hb) <;> decide +kernel

end HighCore82219
