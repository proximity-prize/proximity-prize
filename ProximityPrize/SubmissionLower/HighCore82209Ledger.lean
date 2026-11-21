import ProximityPrize.SubmissionLower.HighCore82209ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82209

open Finset
open HighCore82209_3
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
  | .h2367 => [![6567, 87314, 420366, 2497175], ![5250, 87314, 420366, 2497175], ![(8893/3), (199282/3), 305238, (6052336/3)], ![(15365/8), (92055/2), 292656, (2729727/2)], ![(7201/5), (835958/25), (3862923/16), 1313316], ![(10915/9), (929315/36), (4262989/25), (25576727/25)], ![(48824/49), (983960/49), (2319667/18), (10668685/12)], ![(71238/121), (1586592/121), (2442338/27), (51461516/81)], ![(109750/289), (2670270/289), (12585601/169), (51461516/81)], ![(109750/289), (2670270/289), (12585601/169), (54872490/169)], ![(94627/288), (2269355/288), (20892516/361), (54872490/169)], ![(142163/512), (7090061/1024), (6436144/125), (54872490/169)], ![(247145/1156), (7090061/1024), (6436144/125), (54872490/169)], ![(247145/1156), (9324391/1500), (16738933/400), (5461793/21)], ![(247145/1156), (28128321/5329), (128054126/3481), (207707946/961)], ![(247145/1156), (241852/49), (21421008/625), (1453970826/6889)], ![(247145/1156), (24927520/5329), (451104246/14161), 183764]]
  | .h2395 => [![6465, 76473, 368649, 1941924], ![5001, 76473, 368649, 1941924], ![(24326/9), (162202/3), (749773/3), 1589610], ![(7177/4), (146275/4), (749773/3), 1087849], ![(32959/25), (677857/25), (1556469/8), 1087849], ![(4651/4), (81639/4), (3376554/25), (20086332/25)], ![(45508/49), (829357/49), 111899, (13165781/18)], ![(6640/11), (1287032/121), (5951104/81), (4033120/9)], ![(102974/289), (2257951/289), (10378441/169), (4033120/9)], ![(102974/289), (2699397/361), (270174/5), (60264729/256)], ![(58697/192), (642821/96), (17689956/361), (60264729/256)], ![(71797/256), (2932557/512), (129596/3), (60264729/256)], ![(222162/1225), (2932557/512), (129596/3), (60264729/256)], ![(63671/400), (2932557/512), (129596/3), (60264729/256)], ![(63671/400), (44374703/8427), (6032480/169), (2107292/15)], ![(63671/400), (13083853/3042), (119153405/3844), (2107292/15)], ![(63671/400), (19416137/4608), (18457696/625), (2107292/15)], ![(63671/400), (67598177/16384), (302768859/10609), (2107292/15)]]
  | .h7773 => [![132, 1281, 7413, 32634], ![(175/3), (1214/3), (19047/4), 14402], ![(463/9), (2984/9), (24215/8), (136983/16)], ![(2131/50), (14437/50), (128346/49), (379095/49)]]

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
  | .h2367 => [191781416, 181334098, 146945353, 129133717, 142854071, 126933736, 108435966, 83564016, 76096659, 62793769, 57314222, 61759645, 64650307, 86967680, 99661658, 138528547, 152548466]
  | .h2395 => [154089096, 145906218, 125335673, 118372580, 106535322, 96850293, 81950248, 68732466, 76096659, 64566862, 60877327, 45499204, 101462212, 73472636, 71656214, 78915054, 101462212, 135687751]
  | .h7773 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2367 => [1967552, 2093401, 2614926, 3005033, 2704532, 3066467, 3628512, 4765357, 5249969, 6403733, 7034913, 6509618, 6213640, 4563461, 3964779, 2799269, 2521865]
  | .h2395 => [2596865, 2743971, 3236455, 3438733, 3843290, 4247847, 5056960, 6068351, 5461517, 6472908, 6877465, 9269461, 4045568, 5663795, 5813819, 5259238, 4045568, 2976792]
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
  | .h2367 => [6, 6, 7, 8, 8, 9, 10, 13, 14, 17, 19, 17, 17, 12, 11, 8, 7]
  | .h2395 => [7, 8, 9, 9, 10, 11, 13, 16, 14, 17, 18, 24, 11, 15, 15, 14, 11, 8]
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
  | .h2367, false => [![0, 0, 0, 0], ![17308, 394, 104, 0], ![17594, 446, 119, 0], ![19998, 466, 125, 0], ![21289, 505, 135, 0], ![21439, 566, 150, 0], ![21495, 636, 170, 0], ![28558, 745, 199, 0], ![36703, 973, 260, 0], ![36703, 973, 260, 0], ![46682, 1300, 346, 0], ![57915, 1591, 424, 0], ![94440, 1591, 424, 0], ![94440, 2226, 590, 0], ![116184, 3283, 879, 0], ![146069, 4525, 1211, 0], ![210016, 6637, 1776, 0], ![250000, 7477, 2013, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![3319352748128, 109616267920, 19945267264, 204625408], ![3319352748128, 117706304902, 21578757662, 249114719], ![3319352748128, 120769824646, 21578757662, 326865750], ![3319352748128, 129186674622, 21578757662, 405679455], ![3319352748128, 138837865734, 21578757662, 405679800], ![3319352748128, 146643564261, 21578757662, 521299390], ![3319352748128, 184407840366, 21578757662, 722073888], ![3319352748128, 256210685539, 21726644160, 1238992820], ![3319352748128, 256210685539, 21726644160, 1238992820], ![3319352748128, 380570963606, 21726644160, 2215691618], ![3319353167130, 498613913597, 24301230128, 2982803112], ![5832580873800, 701108307630, 24301230128, 2982803112], ![5832580873800, 701108307630, 38143681130, 3666047600], ![10104252933120, 815716046264, 76444590720, 4011282219], ![14557478722402, 1030100306201, 120690267838, 4801347369], ![29093211326752, 1507305244743, 246026699472, 4971501744], ![38137116500000, 1771071130282, 307080062058, 5076514245]]
  | .h2395, false => [![0, 0, 0, 0], ![13592, 379, 101, 0], ![14451, 423, 112, 0], ![15860, 452, 120, 0], ![17279, 481, 128, 0], ![17279, 573, 153, 0], ![17531, 625, 167, 0], ![22160, 764, 204, 0], ![30224, 934, 249, 0], ![31437, 1045, 279, 0], ![39324, 1221, 329, 0], ![46182, 1604, 430, 0], ![79898, 1604, 430, 0], ![169975, 1604, 430, 0], ![169975, 2470, 661, 0], ![169975, 3811, 1019, 0], ![169975, 4575, 1223, 0], ![169975, 6023, 1607, 0], ![239942, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2094378992832, 93696356464, 15562998696, 262283365], ![2108490756318, 101371455135, 16341496416, 307324752], ![2108490756318, 107981900496, 16341496416, 388374600], ![2108490756318, 116355078487, 16341496416, 440157824], ![2108490756318, 125162346576, 16341496416, 588023370], ![2108490756318, 135000438882, 16341496416, 709390449], ![2108490756318, 174672223072, 16717850592, 1031619840], ![2108490756318, 247605963868, 17114384034, 1511019399], ![2392250668983, 251214718584, 21230967861, 1523763243], ![2539027281288, 333376772694, 21242497598, 2129586732], ![2811436715514, 415262321138, 26177250610, 2957309950], ![3635295401192, 801534829134, 26177250610, 3309197577], ![17246039484700, 826242802392, 36424934108, 3309197577], ![17246039484700, 826242802392, 48565412396, 3743768495], ![17246039484700, 828795720669, 73017682066, 5924281561], ![17246039484700, 969840503692, 96513111042, 6432048074], ![17246039484700, 1228917728860, 163049774684, 6501227776], ![32557190350442, 1838837506352, 300955431718, 6602524656]]
  | .h7773, false => [![0, 0, 0, 0], ![379, 44, 9, 0], ![593, 74, 15, 0], ![995, 117, 24, 0], ![1077, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [191781416, 12347318, 10286232, (57609275/8), (2350903133/400), (475677733/90), (11433966743/882), (3950932900/297), 0, (645457655514/48841), (272862667345/25992), (5192503575/512), (1656815093571/128000), (40425066434167/1734000), (539491843610105045/21444087844), (307720959540551/7080500), (1511340672339978/75463969)]
  | .h2367, true => [40264521986044480, 1504134908888441, (1081079705582224/3), (989953023049215/2), (8068001746955796/25), (19187130865308307/60), (275430219639935485/294), (12577552196086777660/9801), 0, (71609398494251775990/48841), (23337580666062960021547/17570592), (2150273586778660433/1024), (19742965137463842672/21125), (6712855390028019128233/2023000), (40000448697562119233190193427/10303884209042), (1194398276770700226043501451/121943911250), (387245083514881534061760/75463969)]
  | .h2395, false => [154089096, 11715810, (66381460/9), (33635575/6), (1471695877/200), (81129756/25), (528810042/49), (10870527920/1089), (153447347357/48841), (712360255086/104329), (41632421249/4332), (605176913/64), (20011686474/1225), (3824393533/256), (9418592791289/474721), (14045957383261/1461681), (6278997530189/360000), (164777180262535937/4345446400)]
  | .h2395, true => [26952019924106316, 1031970106249737, 486246801694254, (1450115924414229/4), (9991452983769123/25), (14915289107447631/50), (279086405732487229/294), (3331468417332708160/3267), (56823955222964041511/146523), (108156121386044145571557/133541120), (148086292896336473551/138624), (646740068150844335/256), (2871890783959886485403/940800), (80224566068639259/128), (8492300566254803644807/7120815), (20555197303942054244879/14616810), (183980447468516268247/60000), (29017391288478216342757559/3259084800)]
  | .h7773, false => [173109, (319163/6), (4476919/72), (7687867/245)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (254551435087189681492707048702377/609261859721958258816000)
  | .h2367, true => (48877835877202014302082647434030478781138442091737/665529803154350012608796626560000)
  | .h2395, false => (32675534011176076025103656081976935867/91969534274247246430894080000)
  | .h2395, true => (94840965106615290133055390779268536280879489/1738919765689548777054720000)
  | .h7773, false => (5642353559/17640)
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
end HighCore82209
