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

private def historyTable : Band → List Mass
  | .h2367 => [![7214, 98589, 476098, 2754758], ![6320, 98589, 476098, 2754758], ![(22179/4), 98589, 476098, 2754758], ![(9749/3), (252397/3), (3525425/9), 2754758], ![2228, (219319/4), 318784, 1732802], ![(42644/25), (1016977/25), (1171937/4), 1423249], ![(3017/2), (543365/18), (5033014/25), (6242052/5)], ![(64725/64), (691487/32), 137189, (44151068/49)], ![(64725/64), (1525153/81), 137189, (22159665/32)], ![(101371/144), (231143/16), (9528633/100), (3242673/5)], ![(154201/225), (2734144/225), (6311521/72), (88663585/144)], ![(154201/225), (2734144/225), (6311521/72), 510721], ![(43099/100), (79091/8), (1909232/25), 510721], ![(43099/100), (79091/8), (1909232/25), (20155610/49)], ![(43099/100), (79091/8), (21952124/289), (7859683/27)], ![(43099/100), (2670611/288), (589747/9), (7859683/27)], ![(79873/196), (6724209/784), (30744223/529), (7859683/27)], ![(396013/1156), (4497525/578), (4600237/81), (7859683/27)], ![(198821/726), (4497525/578), (4600237/81), (7859683/27)], ![(371865/1681), (4497525/578), (4600237/81), (7859683/27)], ![(371865/1681), (14934523/2116), (68851336/1369), (7859683/27)], ![(326146/1681), (14934523/2116), (68851336/1369), (7859683/27)], ![(326146/1681), (6703733/972), (90504729/1936), (132046285/529)], ![(326146/1681), (33553667/5329), (150420728/3481), (132046285/529)], ![(191751/1156), (33553667/5329), (150420728/3481), (132046285/529)], ![(191751/1156), (28589901/4802), (65503683/1600), (132046285/529)]]
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
  | .h2367 => [245858392, 237904013, 235157908, 190884023, 146945236, 129133696, 141850221, 125952046, 117748273, 91462005, 120955187, 94038399, 118878111, 86040288, 74517035, 72415687, 76420209, 68830860, 75334442, 79003488, 103936882, 87307779, 115173299, 155228560, 145188267, 169863187]
  | .h2395 => [155241934, 146873295, 133169153, 118372580, 106535322, 96850293, 81950248, 68732466, 76096659, 64566862, 60877327, 46768174, 112142444, 73472636, 72544277, 77435132, 101462212, 135401388]
  | .h7773 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2367 => [1481374, 1546734, 1569299, 1979264, 2616120, 3006404, 2727762, 3095291, 3324485, 4339040, 3234892, 4209197, 3292920, 4620577, 5363937, 5530847, 5230030, 5827046, 5304972, 5051726, 3786257, 4548402, 3396423, 2478481, 2654619, 2235305]
  | .h2395 => [2578234, 2723298, 3035694, 3440453, 3845212, 4249971, 5059489, 6071386, 5464248, 6476145, 6880904, 9018904, 3642833, 5666628, 5743342, 5368137, 4047592, 2984809]
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
  | .h2367 => [5, 5, 5, 6, 7, 8, 8, 9, 9, 12, 9, 12, 9, 13, 15, 15, 14, 16, 14, 14, 10, 12, 9, 7, 8, 7]
  | .h2395 => [7, 8, 8, 9, 10, 11, 13, 16, 14, 17, 18, 23, 10, 15, 15, 14, 11, 8]
  | .h7773 => []

private def peak (b : Band) (i : ℕ) : ℕ := (peakTable b)[i]?.getD 0

private theorem rates_check (b : Band) (hb : start b < 7827) :
    ∀ i : Fin (laterCount b+1), rateCheck (finish b) (rate0 b i) (rate1 b i) (peak b i) = true := by
  cases b <;> try (simp [start] at hb) <;> intro i <;> fin_cases i <;> decide +kernel

private theorem rate_valid (b : Band) (hb : start b < 7827) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i) :=
  rate_of_check (rates_check b hb i)


private def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeight b (rate0 b) (rate1 b) else cutWeight b 0

private def registerTable : Band → Bool → List Mass
  | .h2367, false => [![0, 0, 0, 0], ![19408, 470, 125, 0], ![22363, 470, 125, 0], ![22693, 486, 129, 0], ![23656, 540, 143, 0], ![25214, 583, 155, 0], ![25214, 696, 186, 0], ![27838, 770, 205, 0], ![27838, 910, 244, 0], ![33516, 974, 261, 0], ![35969, 1356, 365, 0], ![35969, 1356, 365, 0], ![46380, 1356, 365, 0], ![46380, 1356, 365, 0], ![46507, 1447, 388, 0], ![50532, 1648, 448, 0], ![60968, 1718, 461, 0], ![71408, 1953, 526, 0], ![96501, 1953, 526, 0], ![117552, 1953, 526, 0], ![117552, 2561, 683, 0], ![263168, 2561, 683, 0], ![263168, 2988, 799, 0], ![263168, 3966, 1070, 0], ![446413, 3966, 1070, 0], ![446413, 5113, 1369, 0], ![450000, 5610, 1510, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![4771619671936, 144303950832, 30732299000, 185171750], ![5320247442719, 144303950832, 30732299000, 185171750], ![5336438406244, 149898845495, 30732299000, 202439571], ![5336438406244, 149898845495, 30732299000, 283034752], ![5336438406244, 151631922268, 30732299000, 405498600], ![5336438406244, 162613990792, 30732299000, 559191144], ![5336438406244, 185160108726, 30732299000, 559191210], ![5336438406244, 200247587375, 30732299224, 755251004], ![5336438406244, 226110257162, 30732299253, 867690585], ![5336438406244, 280093408540, 33383631825, 1583749600], ![5336438406244, 280093408540, 33383631825, 1583749600], ![5336438406244, 320481704328, 33383631825, 1583749600], ![5336438406244, 320481704328, 33383631825, 1583749600], ![5336438406244, 339389471275, 33383631825, 1792783876], ![5336438406244, 393854538164, 33383631825, 2403043776], ![5336438406244, 461614830162, 33383631825, 2549720467], ![5457014284272, 522714650417, 40197029934, 2750995780], ![6642246820860, 669760738506, 40197029934, 2750995780], ![8855714325984, 766368836134, 40197029934, 2750995780], ![8855714325984, 766368836134, 53959382304, 3450328858], ![27352861362176, 1168645095650, 53959382304, 3450328858], ![27352861362176, 1168645095650, 69758915421, 3634173198], ![27352861362176, 1168645095650, 123235429930, 3634173198], ![69296047155280, 1714611636733, 157867445520, 3634173198], ![69296047155280, 1714611636733, 198762737523, 3634173411], ![76438434150000, 1958819729070, 256493412370, 3634173411]]
  | .h2395, false => [![0, 0, 0, 0], ![13793, 379, 101, 0], ![14677, 423, 112, 0], ![16131, 452, 120, 0], ![17600, 481, 128, 0], ![17600, 573, 153, 0], ![17833, 625, 167, 0], ![22588, 764, 204, 0], ![30922, 934, 249, 0], ![32132, 1045, 279, 0], ![40307, 1221, 329, 0], ![47252, 1604, 430, 0], ![83679, 1604, 430, 0], ![187144, 1604, 430, 0], ![187144, 2470, 661, 0], ![187144, 3811, 1019, 0], ![187144, 4575, 1223, 0], ![187144, 6023, 1607, 0], ![229924, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![2141251995662, 94398274548, 15679435334, 260401634], ![2155659350715, 102097248531, 16449809040, 305009376], ![2155659350715, 109161237070, 16449809040, 364283280], ![2155659350715, 117489183780, 16449809040, 440377984], ![2155659350715, 126286451510, 16449809040, 588317436], ![2155659350715, 136321165968, 16449809040, 709745157], ![2155659350715, 176893727004, 16717850592, 1032135756], ![2155659350715, 251935521136, 17114384034, 1511775114], ![2445137846988, 255098225391, 21230967861, 1524525192], ![2602496506634, 339870115017, 21242497598, 2130651705], ![2876575455404, 422783708316, 26177250610, 2958788720], ![3913514032146, 817315452802, 26177250610, 3219748728], ![20986785539936, 834920917456, 40259137396, 3219748728], ![20986785539936, 834920917456, 48565412396, 3745641108], ![20986785539936, 837401222761, 73922618263, 5852465498], ![20986785539936, 989461275699, 94703166436, 6565231551], ![20986785539936, 1243081727388, 163049774684, 6565231551], ![31132028734512, 1808485928260, 300320278584, 6620306362]]
  | .h7773, false => [![0, 0, 0, 0], ![383, 44, 9, 0], ![599, 74, 15, 0], ![1006, 117, 24, 0], ![1006, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [245858392, 18675600, (10623167/2), (118409125/9), (38617245/4), (1367924779/100), (2253876419/225), (67005013/8), (24052705715/2592), (61758519377/3600), 0, (1605386611/225), 0, (542177859/200), (19142043361/2312), (21595590929/3600), (4167123283835/414736), (9937154209/1156), (1395126957/242), (319473609001/23409), (54149493840/1681), (25630143097665/2896804), (3044411113951/156816), (59764623770/1681), (373645986900657/18550249), (87012675010593/9329600)]
  | .h2367, true => [63790935970910852, 3467327511348560, (2755754331912275/4), 222020219621198, (1228919067745971/4), (16637080090218348/25), (30626932135798663/45), (112600999681054097/224), (488015472937609823/864), (299377803940015127/200), 0, (110427416598985472/225), 0, (106981982334160553/392), (154679403236476873/216), (289887388475589415/432), (3836192774223376809671/3732624), (896027203588391547/578), (47484459524150893076/34969), (26599897164331504/27), (150328664615982129917/21689), (31349259830601583604/36963), (439988859409237551/176), (407621643353648038765059817/31182968569), (3254143383589084551441/1841449), (5553528224769070957929789/1110222400)]
  | .h2395, false => [155241934, 11824313, (67786406/9), (824699351/144), (2981775423/400), (976641253/300), (1068376455/98), (11122695620/1089), (155357793395/48841), (2191612422854/312987), (169240884833/17328), (2615349319/256), (4597198266/245), (52095567943/3456), (9511536246356/474721), (23821774867351/2436135), (30196562466991/1707552), (1009598025781507/29736960)]
  | .h2395, true => [27318965859232600, 1029504726884069, (4323539363727958/9), (3115425260182637/8), (1999216307848624/5), (45846036051701357/150), (26917359522520195/28), (3452944898525506768/3267), (515037100032099874582/1318707), (6635041594097727719102/7824675), (25280526813571636755/23104), (169689092994053695/64), (3226299100442571337621/846720), (39480283156952200/81), (5241589748642011684196/4272489), (8325784531074160835311/5846724), (14252027311027717756505/4553472), (443722621779991214271737/55756800)]
  | .h7773, false => [175294, 53674, (4523701/72), (34489488/1225)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (1261035793324192213708440376999441061/2340279092361800206662534720)
  | .h2367, true => (8975612674812044612671822983940690806428770627/81909768232663007233188715200)
  | .h2395, false => (159432520395165451701602072578073/445834834826616332697600)
  | .h2395, true => (64323923213752418070743111470547168528417/1170316441419867873331200)
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
