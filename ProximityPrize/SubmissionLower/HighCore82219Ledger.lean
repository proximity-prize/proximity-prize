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
  | .h2367 => [![7409, 95292, 465616, 2580152], ![(13335/2), 95292, 465616, 2580152], ![(34519/9), (696301/9), (1063253/3), (20175815/9)], ![(8997/4), (214335/4), 310990, (13126275/8)], ![(41833/25), (1015091/25), (4600889/16), 1437601], ![(13727/9), (357739/12), (994263/5), (30261843/25)], ![(4029/4), (175311/8), 132650, (42672368/49)], ![(90802/121), (1852663/121), (8563513/81), (20690696/27)], ![(126326/289), (3296320/289), (15622638/169), (20690696/27)], ![(126326/289), (3296320/289), (15622638/169), 498436], ![(126326/289), (4481668/441), (20181298/289), (25588312/81)], ![(142973/512), (4794503/512), (43576148/625), (25588312/81)], ![(142973/512), (8793564/961), (19674397/338), (67201540/243)], ![(142973/512), (13530836/1849), (1740486/35), (67201540/243)], ![(142973/512), (1822449/284), (71940303/1682), (105189909/400)], ![(516397/2592), (1822449/284), (71940303/1682), (105189909/400)], ![(516397/2592), (19602221/3267), (3291791/81), (99022401/400)]]
  | .h2395 => [![6465, 73163, 353264, 1808866], ![5001, 73163, 353264, 1808866], ![(24326/9), (472282/9), (2182528/9), (13218095/9)], ![(7177/4), 35635, (2182528/9), 982081], ![(32959/25), (663122/25), (761151/4), 982081], ![(4651/4), (120575/6), (3323628/25), (19113281/25)], ![(45508/49), (814384/49), 106088, (2073344/3)], ![(6640/11), (1278176/121), (5908828/81), (11741684/27)], ![(102974/289), (2237623/289), (10279541/169), (11741684/27)], ![(102974/289), (2710589/361), (4069354/75), (60017565/256)], ![(58697/192), (642487/96), (17674020/361), (60017565/256)], ![(71797/256), (735103/128), (26604532/625), (60017565/256)], ![(222162/1225), (735103/128), (26604532/625), (60017565/256)], ![(63671/400), (735103/128), (26604532/625), (60017565/256)], ![(63671/400), (45025001/8427), (6032480/169), (289775068/2025)], ![(63671/400), (66336533/15210), (120801595/3844), (289775068/2025)], ![(63671/400), (9853693/2304), (176620736/5929), (289775068/2025)], ![(63671/400), (8588061/2048), (10442510/363), (289775068/2025)]]
  | .h7773 => [![132, 1287, 7443, 32886], ![(175/3), (1229/3), (9637/2), (58905/4)], ![(463/9), (673/2), (49167/16), (70551/8)], ![(2131/50), (7341/25), (130551/49), (55970/7)]]

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
  | .h2367 => [243874541, 251183851, 209667385, 192712363, 152964015, 146945236, 129133696, 110383908, 160628300, 97719044, 82600267, 79293208, 85204346, 115661647, 111776252, 129297807, 139993721]
  | .h2395 => [155241934, 146873295, 133169153, 118372580, 106535322, 96850293, 81950248, 68732466, 76096659, 64566862, 60877327, 46768174, 112142444, 73472636, 72544277, 77435132, 101462212, 135401388]
  | .h7773 => []

def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

def rate1Table : Band → List ℚ
  | .h2367 => [1498039, 1439555, 1779185, 1957705, 2516721, 2616756, 3007134, 3563450, 2389336, 4049510, 4825895, 5032951, 4671319, 3383602, 3515133, 3003537, 2769113]
  | .h2395 => [2578378, 2723449, 3035863, 3440644, 3845426, 4250207, 5059770, 6071724, 5464552, 6476505, 6881287, 9019405, 3643035, 5666942, 5743661, 5368435, 4047817, 2984975]
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
  | .h2367 => [5, 4, 5, 6, 7, 7, 8, 10, 7, 11, 13, 14, 13, 9, 10, 8, 8]
  | .h2395 => [7, 8, 8, 9, 10, 11, 13, 16, 14, 17, 18, 23, 10, 15, 15, 14, 11, 8]
  | .h7773 => []

private def peak (b : Band) (i : ℕ) : ℕ := (peakTable b)[i]?.getD 0

theorem rates_check (b : Band) (hb : start b < 7827) :
    ∀ i : Fin (laterCount b+1), rateCheck (finish b) (rate0 b i) (rate1 b i) (peak b i) = true := by
  cases b <;> try (simp [start] at hb) <;> intro i <;> fin_cases i <;> decide +kernel

theorem rate_valid (b : Band) (hb : start b < 7827) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i) :=
  rate_of_check (rates_check b hb i)


def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeight b (rate0 b) (rate1 b) else cutWeight b 0

def registerTable : Band → Bool → List Mass
  | .h2367, false => [![0, 0, 0, 0], ![18724, 478, 128, 0], ![19307, 557, 149, 0], ![23130, 557, 149, 0], ![25165, 577, 154, 0], ![25165, 704, 188, 0], ![28148, 751, 201, 0], ![31413, 948, 254, 0], ![43934, 1114, 298, 0], ![43934, 1114, 298, 0], ![46694, 1432, 383, 0], ![83094, 1606, 429, 0], ![83094, 1763, 472, 0], ![85514, 2478, 664, 0], ![130779, 3836, 1027, 0], ![206097, 3836, 1027, 0], ![206097, 5262, 1405, 0], ![300000, 5262, 1405, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![4566306905684, 144621312834, 31215941248, 191748992], ![4849606611257, 167702893392, 37426393799, 214493695], ![4849606615050, 167702893392, 37426393799, 256202640], ![4849606615050, 167702893392, 37426393799, 301486570], ![4849606615050, 167702912247, 37426393799, 473143548], ![4849606615050, 184012320124, 37426393799, 525967956], ![4849606615050, 216881844150, 37426393799, 763812036], ![4849606615050, 279524285812, 37426393799, 1061908100], ![5382493704700, 279524285812, 37426393900, 1061908100], ![5382493704700, 329021490948, 37426393900, 1550962330], ![6863586586098, 533658947932, 37426393900, 2070308955], ![6863586586098, 533658947932, 37426394176, 2375552872], ![7286164443844, 610599542354, 56575685744, 3101755816], ![15126114533013, 886182163850, 118784511469, 3474959254], ![23036750208444, 1064034619477, 118784511469, 3474959254], ![23036750208444, 1214631218457, 181663418835, 4219969485], ![41998116300000, 1493604168935, 181663418835, 4219969485]]
  | .h2395, false => [![0, 0, 0, 0], ![13214, 379, 101, 0], ![14137, 423, 112, 0], ![15560, 452, 120, 0], ![17006, 481, 128, 0], ![17006, 573, 153, 0], ![17472, 625, 167, 0], ![22196, 764, 204, 0], ![30425, 934, 249, 0], ![31705, 1045, 279, 0], ![39855, 1221, 329, 0], ![46877, 1604, 430, 0], ![81911, 1604, 430, 0], ![177493, 1604, 430, 0], ![177493, 2470, 661, 0], ![177493, 3811, 1019, 0], ![177493, 4575, 1223, 0], ![177493, 6023, 1607, 0], ![225000, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2051366915876, 92907379878, 15679435334, 260416178], ![2076347771415, 100628802298, 16449809040, 305026288], ![2076347771415, 107430485436, 16449809040, 364303560], ![2076347771415, 115448802844, 16449809040, 440402432], ![2076347771415, 124790366308, 16449809040, 588350178], ![2076347771415, 134791049829, 16449809040, 709784569], ![2076347771415, 174916644392, 16717850592, 1032193080], ![2091185278050, 248928325944, 17114384034, 1511859276], ![2412644573595, 252774629815, 21230967861, 1524610008], ![2573312285010, 336957245277, 21242497598, 2130770145], ![2853746457779, 420221323207, 26177250610, 2958953410], ![3830827900514, 801411067941, 26177250610, 3219927585], ![19904498812892, 801411067941, 40259137396, 3219927585], ![19904498812892, 801411067941, 48565412396, 3745848662], ![19904498812892, 835755229522, 73922618263, 5852790559], ![19904498812892, 987891375080, 94703166436, 6565596005], ![19904498812892, 1241785126195, 163049774684, 6565596005], ![30465312300000, 1793826078744, 300320278584, 6620674550]]
  | .h7773, false => [![0, 0, 0, 0], ![385, 44, 9, 0], ![603, 74, 15, 0], ![1015, 117, 24, 0], ![1015, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [243874540, (42386313/2), (131966137/9), (28815395/4), (2986710281/200), (1536473899/180), (117089237/8), (162594529112/9801), 0, (619844431350/48841), (887532816892/42483), (1429833081243/320000), (382387550557201/20788352), (1346206160688719/33134080), (5384220207/256), (3023534413131/119422), (16163742497/864)]
  | .h2367, true => [62642405252125836, (14077523254724371/2), (841512089095742/9), (297204659130375/4), (1233875044057051/5), (165045548910319903/300), (181776014033316867/196), (3879799634936325286/3267), (11376657024333457682/48841), (233605912913156440/289), (3316212138870979943324/1147041), (4881673839374679688/50625), (2399518321952053621691167/1122571008), (3973558705241042932121395/536772096), (121789779151897368717/36352), (91995131528648104428669/23884400), (47493269043092900245/8712)]
  | .h2395, false => [148836951, 11720999, (21924100/3), (100222657/18), (719748271/100), (517208477/150), (520516712/49), (10939865660/1089), (153374526007/48841), (2171612325920/312987), (41824527911/4332), (1257668049/128), (21234688284/1225), (592258650463/40000), (9467718253103/474721), (71205776566091/7308405), (30107321224969/1707552), (643746801884783/18585600)]
  | .h2395, true => [26069507759216778, 1042690695176643, (1331948376139252/3), 360467997146712, (9827013005860258/25), (44071868218095601/150), (134967741296271664/147), (3359445226166780680/3267), (58647179301380382122/146523), (1666740692471943117434927/2003116800), (99693190717004951489/92416), (323121000350911937/128), (107631430304200224348/30625), (122079777805805185/256), (1336344991942825848448691/961310025), (1866152870478642755662843/1315512900), (42645689994386159250167/13660416), (1330258394050215190880603/167270400)]
  | .h7773, false => [174435, (161753/3), (9118231/144), (34743216/1225)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (200590843132058269299668246926022899/398185684774498630769760000)
  | .h2367, true => (39413752337128848826210748930736897239877943/398185684774498630769760000)
  | .h2395, false => (1132617139055042543677967357530349/3250879003944077425920000)
  | .h2395, true => (173142160453738782875845130167699450138169/3250879003944077425920000)
  | .h7773, false => (56454266479/176400)
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

private theorem charge_eq (b : Band) (mode : Bool) :
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
end HighCore82219
