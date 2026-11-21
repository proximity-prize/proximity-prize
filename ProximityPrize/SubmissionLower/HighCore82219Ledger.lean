import ProximityPrize.SubmissionLower.HighCore82219ScheduleData
import ProximityPrize.SubmissionLower.HighCore82219PrefixGeometry

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

private def historyTable : Band → List Mass
  | .h2367 => [![7188, 95700, 467458, 2686363], ![(12215/2), 95700, 467458, 2686363], ![(31285/9), (696512/9), (3188408/9), (6963968/3)], ![(4559/2), (201611/4), 313456, 1523951], ![(45016/25), (901792/25), (4181357/16), 1523951], ![(2709/2), (1077371/36), (4986204/25), (31453284/25)], ![(54454/49), (1156118/49), (2700517/18), 1127613], ![(80814/121), (1824854/121), (8428618/81), (63249928/81)], ![(121632/289), (3177066/289), (1160477/13), (63249928/81)], ![(121632/289), (3177066/289), (785015/9), (65723700/169)], ![(121632/289), (1142533/125), (24717707/400), (862988/3)], ![(296679/1024), (8628207/1024), (24717707/400), (862988/3)], ![(126009/578), (8628207/1024), (24717707/400), (862988/3)], ![(126009/578), (12583070/1681), (3334497/68), (862988/3)], ![(126009/578), (1668383/250), (75238384/1681), (6801664/25)], ![(126009/578), (16423161/2738), (24404879/600), (244568520/961)], ![(126009/578), (55645411/9801), (252459989/6561), (101943094/441)], ![(126009/578), (119804590/21609), (45257696/1225), (831461290/3969)]]
  | .h2395 => [![6465, 76270, 367959, 1945556], ![5001, 76270, 367959, 1945556], ![(24326/9), (491362/9), (2270863/9), (14383460/9)], ![(7177/4), (591879/16), (2270863/9), 1069156], ![(32959/25), (686784/25), (3153327/16), 1069156], ![(4651/4), (247633/12), (3413346/25), (20292532/25)], ![(45508/49), (837486/49), (222159/2), (8863001/12)], ![(6640/11), (1304416/121), (6030580/81), (36886204/81)], ![(102974/289), (134815/17), (10531457/169), (36886204/81)], ![(102974/289), (2747536/361), (4124824/75), 240990], ![(58697/192), (1308037/192), (17994458/361), 240990], ![(71797/256), (1490901/256), (3517192/81), 240990], ![(222162/1225), (1490901/256), (3517192/81), 240990], ![(63671/400), (1490901/256), (3517192/81), 240990], ![(63671/400), (45250412/8427), (6059120/169), (6501272/45)], ![(63671/400), (11096204/2535), (121242971/3844), (6501272/45)], ![(63671/400), (9882907/2304), (177144194/5929), (6501272/45)], ![(63671/400), (68857725/16384), (10469446/363), (6501272/45)]]
  | .h7773 => [![132, 1298, 7514, 33536], ![(175/3), (1225/3), 4804, (58599/4)], ![(463/9), (1004/3), (24445/8), (139567/16)], ![(2131/50), (7288/25), (129594/49), (386304/49)]]

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
  | .h2367 => [237194346, 232266110, 197156442, 139195001, 138433599, 129133617, 138742960, 108751389, 108817484, 75095218, 72675350, 86968106, 71174947, 75746346, 102975694, 124910693, 170832891, 168146452]
  | .h2395 => [155241934, 146873295, 133169153, 118372580, 106535322, 96850293, 81950248, 68732466, 76096659, 64566862, 60877327, 46768174, 112142444, 73472636, 72544277, 77435132, 101462212, 135401388]
  | .h7773 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2367 => [1552177, 1592662, 1903195, 2785245, 2801924, 3005653, 2795147, 3618317, 3616025, 5320151, 5508843, 4564377, 5627991, 5275220, 3825842, 3123602, 2220354, 2263264]
  | .h2395 => [2577089, 2722088, 3034345, 3438925, 3843504, 4248083, 5057241, 6068689, 5461820, 6473268, 6877847, 9014896, 3641214, 5664110, 5740790, 5365752, 4045793, 2983482]
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
  | .h2367 => [5, 5, 6, 8, 8, 9, 8, 10, 10, 14, 15, 12, 15, 14, 11, 9, 6, 7]
  | .h2395 => [7, 8, 8, 9, 10, 11, 13, 16, 14, 17, 18, 23, 10, 15, 15, 14, 11, 8]
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
  | .h2367, false => [![0, 0, 0, 0], ![19545, 439, 117, 0], ![19784, 505, 135, 0], ![21314, 549, 146, 0], ![21671, 635, 168, 0], ![24708, 635, 168, 0], ![24813, 714, 191, 0], ![32074, 844, 226, 0], ![42629, 1077, 286, 0], ![42629, 1078, 286, 0], ![50764, 1571, 418, 0], ![70888, 1665, 447, 0], ![146812, 1665, 447, 0], ![146812, 2109, 560, 0], ![146812, 2710, 717, 0], ![146812, 4054, 1083, 0], ![166048, 5262, 1405, 0], ![245740, 7356, 1962, 0], ![245740, 7477, 2013, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![4635963492570, 134465617359, 27751738482, 181604709], ![4635963492570, 148803610558, 31355924850, 215009370], ![4635963492570, 148803610558, 31355924850, 277866470], ![4635963492570, 148803610558, 31355924850, 467921160], ![4635963492570, 155750937567, 31355924850, 467921308], ![4635963492570, 166780670427, 31355924850, 574079723], ![4635963492570, 206750603118, 31355924850, 631703222], ![4635963492570, 271370481346, 31355924850, 1034838662], ![4635963492570, 271370481346, 31355924850, 1034838662], ![4635963492570, 388046732842, 31389801124, 2223823118], ![5151810210800, 511515320334, 32485881450, 2462452821], ![12767961578072, 794991516340, 33221816492, 2462452821], ![12767961578072, 794991516340, 39857970320, 3151674960], ![12767961578072, 794991516340, 54310130082, 3782332740], ![12965051777376, 899152274644, 111522676602, 4143386886], ![20741170751264, 1175947931462, 175499523665, 4388660810], ![41980474634340, 1802276538156, 335174132142, 4388660810], ![41980474634340, 1802276538156, 338478807876, 4555950432]]
  | .h2395, false => [![0, 0, 0, 0], ![13793, 379, 101, 0], ![14677, 423, 112, 0], ![16131, 452, 120, 0], ![17600, 481, 128, 0], ![17600, 573, 153, 0], ![17833, 625, 167, 0], ![22588, 764, 204, 0], ![30922, 934, 249, 0], ![32132, 1045, 279, 0], ![40307, 1221, 329, 0], ![47252, 1604, 430, 0], ![83679, 1604, 430, 0], ![187144, 1604, 430, 0], ![187144, 2470, 661, 0], ![187144, 3811, 1019, 0], ![187144, 4575, 1223, 0], ![187144, 6023, 1607, 0], ![229924, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2141251995662, 94382481563, 15679435334, 260285989], ![2155659350715, 102079489361, 16449809040, 304873856], ![2155659350715, 109139476351, 16449809040, 364121400], ![2155659350715, 117462290980, 16449809040, 440182400], ![2155659350715, 126257471874, 16449809040, 588056112], ![2155659350715, 136287497264, 16449809040, 709429861], ![2155659350715, 176842949180, 16717850592, 1031677164], ![2155659350715, 251852124502, 17114384034, 1511103561], ![2445137846988, 255020208895, 21230967861, 1523847780], ![2602496506634, 339754151778, 21242497598, 2129705172], ![2876575455404, 422639258952, 26177250610, 2957474210], ![3913514032146, 816980067370, 26177250610, 3218317872], ![20986785539936, 834617931320, 40259137396, 3218317872], ![20986785539936, 834617931320, 48565412396, 3743976710], ![20986785539936, 837151976577, 73922618263, 5849865010], ![20986785539936, 989179065804, 94703166436, 6562314696], ![20986785539936, 1242800838724, 163049774684, 6562314696], ![31132028734512, 1808180819112, 300320278584, 6617363076]]
  | .h7773, false => [![0, 0, 0, 0], ![383, 44, 9, 0], ![599, 74, 15, 0], ![1006, 117, 24, 0], ![1006, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [237194346, (32380273/2), (113585066/9), 12044450, (136713592/25), (6384384887/900), (14453731667/882), (4991653624/297), (3177066/289), (17649560314/867), (6427849071483/578000), (5631264099/256), (68632888681/6400), (1394275349509/114308), (5326814893056/210125), (2912325013990879/118692300), (11631040303093177/229431609), (1380299725486/540225)]
  | .h2367, true => [59652293504051583, 3146688745694787, (437734832972800/3), 289634034880190, (6265049556718828/25), (6954716099387191/15), (49393831965170001/49), (4212320699479407464/3267), 0, (768369260521756003166/439569), (1284908954602583059631/867000), (59400143433194424833/12800), (60833974324902499/100), (30263509442416777/34), (206289304556663456750724/60726125), (1373370496169404721422166377/228126600600), (3287857984922565989921165/229431609), (15591893912377167484/99225)]
  | .h2395, false => [155241934, 11824313, (67786406/9), (824699351/144), (2981775423/400), (976641253/300), (1068376455/98), (11122695620/1089), (155357793395/48841), (2191612422854/312987), (169240884833/17328), (2615349319/256), (4597198266/245), (52095567943/3456), (9511536246356/474721), (23821774867351/2436135), (30196562466991/1707552), (1009598025781507/29736960)]
  | .h2395, true => [27317536334443030, 1029316098028619, (4321194006602620/9), (6227236392053891/16), (9992891175781696/25), (45824950080778183/150), (11531232134577199/12), (1150493085910662580/1089), (515089845641248998460/1318707), (6632274284703997650452/7824675), (1579624640633893185/1444), (84808065927065909/32), (3226458866394901177141/846720), (39475724372739220/81), (5242244839305392639348/4272489), (3201797569882852440391/2248740), (5344519918951490547101/1707552), (98603718499640013668421/12390400)]
  | .h7773, false => [175294, 53674, (4523701/72), (34489488/1225)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (5104786733934188722344825373397/10141601917949171208000)
  | .h2367, true => (26762175895727334565719831119959728344180189/268912232798727664770624000)
  | .h2395, false => (159432520395165451701602072578073/445834834826616332697600)
  | .h2395, true => (1063109389359650820796007853966887363221/19344073411898642534400)
  | .h7773, false => (28219754461/88200)
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
end HighCore82219
