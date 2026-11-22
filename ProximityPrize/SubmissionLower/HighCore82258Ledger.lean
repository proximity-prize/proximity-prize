import ProximityPrize.SubmissionLower.HighCore82258ScheduleData
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

set_option autoImplicit true
set_option maxRecDepth 18000

namespace HighCore82258

open Finset
open HighCore82258_3
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
  | .h2367 => [![7409, 95685, 468356, 2616723], ![(13335/2), 95685, 468356, 2616723], ![(34519/9), (717586/9), (1095283/3), (20751410/9)], ![(8997/4), (223701/4), 307154, (13701983/8)], ![(41833/25), (212091/5), (600487/2), 1411344], ![(13727/9), (555625/18), (5146022/25), (6295464/5)], ![(4029/4), (1459647/64), (946452/7), (44697620/49)], ![(90802/121), (1919771/121), (8870693/81), (21668845/27)], ![(126326/289), (3437864/289), (16293555/169), (21668845/27)], ![(126326/289), (3437864/289), (16293555/169), (2507022/5)], ![(126326/289), (1565281/147), (21135547/289), (3024280/9)], ![(142973/512), (10289273/1024), (21135547/289), (3024280/9)], ![(142973/512), (300656/31), (41683605/676), (24148450/81)], ![(142973/512), (14253992/1849), (64134474/1225), (24148450/81)], ![(142973/512), (68182281/10082), (151598763/3364), (13549761/49)], ![(516397/2592), (68182281/10082), (151598763/3364), (13549761/49)], ![(516397/2592), (62088038/9801), (281399422/6561), (1934878876/7225)]]
  | .h2395 => [![6465, 66285, 320052, 1511053], ![5001, 66285, 320052, 1511053], ![(24326/9), (412934/9), (1909106/9), 1158905], ![(7177/4), (498537/16), (1909106/9), 833569], ![(32959/25), (579819/25), (332949/2), 833569], ![(4651/4), 18036, (2983968/25), (15725232/25)], ![(45508/49), (104523/7), 96552, 562068], ![(6640/11), (1155115/121), (1780499/27), (29378597/81)], ![(102974/289), (1995995/289), (9171737/169), (29378597/81)], ![(102974/289), (2459621/361), (11078266/225), (3286969/16)], ![(58697/192), (192335/32), (835596/19), (3286969/16)], ![(71797/256), (1335989/256), (3153020/81), (3286969/16)], ![(222162/1225), (1335989/256), (3153020/81), (3286969/16)], ![(63671/400), (1335989/256), (3153020/81), (3286969/16)], ![(63671/400), (13817559/2809), (5010545/147), 129600], ![(63671/400), (30846406/7605), (112401301/3844), 129600], ![(63671/400), (18342749/4608), (82192675/2888), 129600], ![(63671/400), (31967115/8192), (286515495/10609), 129600]]
  | .h7773 => [![132, 1367, 7907, 37118], ![(175/3), (1274/3), (9987/2), 15800], ![(463/9), (6245/18), (50735/16), 9375], ![(2131/50), (3033/10), (134877/49), (417644/49)]]

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

private theorem seed_bill_eq (b : Band) (v : ℕ → Mass) :
    weightedBill (laterCount b+1) v (history b) =
    weightedBill (laterCount b+1) v (receipt b) := by
  unfold weightedBill
  apply sum_congr rfl
  intro i hi
  rw [history_eq b i (by simpa using hi)]

private def rate0Table : Band → List ℚ
  | .h2367 => [250703355, 257411712, 209004978, 192250090, 151344180, 146945269, 129133574, 108902784, 133169153, 98027804, 88312895, 79543745, 90425937, 122251912, 122558590, 140293703, 150749576]
  | .h2395 => [130462977, 124891578, 104979955, 96148597, 84495720, 77412251, 70983322, 58375491, 65204041, 55294618, 55343048, 40318770, 69859227, 73472602, 67715749, 71570044, 92491359, 120894836]
  | .h7773 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2367 => [1442921, 1408593, 1785753, 1964514, 2545245, 2618403, 3009031, 3617125, 2920527, 4039025, 4501673, 5018813, 4395088, 3201456, 3192881, 2764278, 2555134]
  | .h2395 => [3096679, 3250241, 3900462, 4279788, 4901219, 5368557, 5870994, 7178684, 6406782, 7590734, 7583560, 10489606, 5963862, 5665340, 6165780, 5822522, 4459098, 3366378]
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
  | .h2367 => [4, 4, 5, 6, 7, 7, 9, 10, 8, 11, 12, 14, 12, 9, 9, 8, 7]
  | .h2395 => [8, 9, 10, 11, 13, 14, 15, 19, 17, 20, 19, 27, 15, 15, 16, 15, 12, 9]
  | .h7773 => []

private def peak (b : Band) (i : ℕ) : ℕ := (peakTable b)[i]?.getD 0

private theorem rates_check (b : Band) (hb : start b < 7773) :
    ∀ i : Fin (laterCount b+1), rateCheck (finish b) (rate0 b i) (rate1 b i) (peak b i) = true := by
  cases b <;> try (simp [start] at hb) <;> intro i <;> fin_cases i <;> decide +kernel

private theorem rate_valid (b : Band) (hb : start b < 7773) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i) :=
  rate_of_check (rates_check b hb i)


open HighCore82268JointRank (splice)
open HighCore82258JointRank (rankCharge rankRounding)

private def billCount (b : Band) (mode : Bool) : ℕ :=
  if mode then lossCount b else laterCount b+1

private def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeights b (rate0 b) (rate1 b) else cutWeight b 0

private def billHistory (b : Band) (mode : Bool) : ℕ → Mass :=
  if mode && jointRank b then splice (stopIndex b) (receipt b 0) (receipt b) else receipt b

private theorem billHistory_eq (b : Band) (i : ℕ) (hi : i < lossCount b) :
    lossHistory b i = billHistory b true i := by
  by_cases hj : jointRank b = true
  · have hs : i < laterCount b + 1 + 1 := by simpa [lossCount, hj] using hi
    by_cases hz : i = 0
    · subst i
      simpa [lossHistory, hj, billHistory, stopIndex, splice, rankMass] using
        history_eq b 0 (Nat.zero_le _)
    · simpa [lossHistory, hj, billHistory, stopIndex, splice, hz] using
        history_eq b (i-1) (by omega)
  · have hs : i < laterCount b + 1 := by simpa [lossCount, hj] using hi
    simpa [lossHistory, hj, billHistory] using history_eq b i (by omega)

private def registerTable : Band → Bool → List Mass
  | .h2367, false => [![0, 0, 0, 0], ![19573, 478, 128, 0], ![20147, 557, 149, 0], ![24446, 557, 149, 0], ![26591, 577, 154, 0], ![26591, 704, 188, 0], ![29660, 751, 201, 0], ![33015, 948, 254, 0], ![46747, 1114, 298, 0], ![46747, 1114, 298, 0], ![49376, 1432, 383, 0], ![91138, 1606, 429, 0], ![91138, 1763, 472, 0], ![91138, 2478, 664, 0], ![139347, 3836, 1027, 0], ![234277, 3836, 1027, 0], ![234277, 5262, 1405, 0], ![315000, 5262, 1405, 0]]
  | .h2367, true => [![0, 0, 0, 0], ![0, (594136424677807941469/3468801700), (28486465151390334/749525), 0], ![4907016767415, (594136424677807941469/3468801700), (28486465151390334/749525), 184693888], ![5186073761664, 171757246755, 38354345088, 209880357], ![5186073761664, 171757246755, 38354345088, 257148432], ![5186073761664, 171757246755, 38354345088, 302535156], ![5186073761664, 171757246755, 38354345088, 478506060], ![5186073761664, 188017729999, 38354345088, 526299003], ![5186073761664, 221761786617, 38354345088, 764293874], ![5186073761664, 290407443751, 38354345088, 1077903250], ![5186073761664, 290407443751, 38354345088, 1077903250], ![5186073761664, 339806713728, 38354345088, 1546946575], ![8048660624510, 552103983244, 38354345088, 1931217717], ![8048660624510, 552103983244, 38354345088, 2368879736], ![8241058194432, 624626211854, 60042822168, 2918338432], ![17035437181464, 915071623664, 125552713624, 3287895312], ![28712658789430, 1120351578457, 125552713624, 3287895312], ![28712658789430, 1261873703838, 197112652715, 3883810590], ![47486116440000, 1548514868408, 199441689048, 3883810590]]
  | .h2395, false => [![0, 0, 0, 0], ![11294, 379, 101, 0], ![12199, 423, 112, 0], ![13413, 452, 120, 0], ![14645, 481, 128, 0], ![14724, 573, 153, 0], ![15613, 625, 167, 0], ![19837, 764, 204, 0], ![26947, 934, 249, 0], ![28359, 1045, 279, 0], ![35496, 1221, 329, 0], ![42333, 1604, 430, 0], ![66559, 1604, 430, 0], ![118401, 1604, 430, 0], ![118401, 2470, 661, 0], ![118401, 3811, 1019, 0], ![118401, 4575, 1223, 0], ![143115, 6023, 1607, 0], ![180000, 8288, 2218, 0]]
  | .h2395, true => [![0, 0, 0, 0], ![1473448862238, 84419360909, 13176760677, 312764579], ![1523552360022, 92478827453, 13987856736, 364026992], ![1523552360022, 99767836466, 13987856736, 468055440], ![1523552360022, 108924970417, 13987856736, 547812864], ![1523552360022, 120581596116, 13987856736, 749886507], ![1523552360022, 132201937316, 13987856736, 896549019], ![1523552360022, 170694165986, 14480597688, 1197682776], ![1573044355977, 247966706342, 14535497259, 1787492316], ![1849121398719, 249828153583, 18191927439, 1787492316], ![1962737760528, 336955422642, 18191929322, 2497351486], ![2342837250984, 409805094472, 23797510640, 3260930800], ![2683577012430, 752164518784, 23797510640, 3744789342], ![8271402336027, 801554928744, 25079462493, 3744789342], ![8271402336027, 801554928744, 48565389922, 3744789740], ![8271402336027, 809513585299, 69002348231, 6282929820], ![8271402336027, 958495353226, 87530163812, 7120944406], ![13236900843285, 1195239265527, 148633613913, 7165770486], ![21761070480000, 1607924440768, 268144746248, 7466626404]]
  | .h7773, false => [![0, 0, 0, 0], ![400, 44, 9, 0], ![625, 74, 15, 0], ![1052, 117, 24, 0], ![1052, 141, 32, 0]]
  | .h7773, true => [![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2367, false => [250703355, 21221736, (49465727/3), (29915665/4), (77976952/5), (3963436673/450), (6737155437/448), (174039148582/9801), 0, (641135633789/48841), (332382457248/14161), (1397495589333/295936), (98354972000/5239), (49792206387464781/1159692800), (6786213445/256), (226204261255233/8478962), (41685115031/2592)]
  | .h2367, true => [(118595826000969528721204977/3468801700), 36839379974466759, (7407002422910205675250773/3468801700), (326959734745250/3), (155472030168423/2), 248355479534976, (25294736275113718/45), (1547142807541223867/1568), (4380428337778477598/3267), 0, (237795103707496198/289), (464039491778647717928/127449), (1323612490821320/9), (245327683397893726289867/108635904), (96691584606965815598426279/11741889600), (5999590136045443337443/1290496), (515979291246941043669141/118705468), (71841907462302938904841/12702096)]
  | .h2395, false => [130462977, 10963017, (18926566/3), (692798029/144), (319987343/50), (364257883/100), (468975447/49), (3224253745/363), (141534309667/48841), (5825297037986/938961), (10742174931/1216), (869677061/128), (235047396/25), (46695212519/3456), (7762528236983/412923), (66242961270179/7308405), (107224967981849/5198400), (13562573265076911/434544640)]
  | .h2395, true => [19811436695808626, 1121842471112781, (1364970481513034/3), (5628903147189783/16), (10969791169215156/25), (7545913873982784/25), 791593232537610, (292572805354230259/297), (1163401543997161519/3757), (146467060583576264646121/187792200), (291066310549025211/304), (253649683013365099/128), (4194583080579978468313/3175200), (592412844200137951/648), (439636025553851552660/412923), (12226022039376071464511/9744540), (144623798099979244847449/41587200), (2708890016994572136980799/434544640)]
  | .h7773, false => [184111, 55826, (9421031/144), (7178484/245)]
  | .h7773, true => [0, 0, 0, 0]

private def credit : Band → Bool → ℚ
  | .h2367, false => (76662785446069131457523240167133141/145915786420590465985305600)
  | .h2367, true => (11211782435408538629017262148139595709854917/105528381250605604864372800)
  | .h2395, false => (5105170273867265712822676249783487321/16554516169364504357560934400)
  | .h2395, true => (192117387128904110378037755200626431318080993/4514868046190319370243891200)
  | .h7773, false => (11806831651/35280)
  | .h7773, true => 0

private def register (b : Band) (mode : Bool) (i : ℕ) : Mass :=
  (registerTable b mode)[i]?.getD (fun _ => 0)

private def charge (b : Band) (mode : Bool) (i : ℕ) : ℚ :=
  (chargeTable b mode)[i]?.getD 0

private theorem register_step (b : Band) (mode : Bool) :
    ∀ i : Fin (billCount b mode), ∀ k : Fin 4,
      max (register b mode i k) (tariffWeights b mode i k) = register b mode (i+1) k := by
  cases b <;> cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (b : Band) (mode : Bool) (i : ℕ) (hi : i ≤ billCount b mode) :
    running (tariffWeights b mode) i = register b mode i := by
  induction i with
  | zero => funext k; cases b <;> cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running, ih (by omega : i ≤ billCount b mode)]
    exact register_step b mode ⟨i,by omega⟩ k

private theorem charge_eq (b : Band) (mode : Bool) :
    ∀ i : Fin (billCount b mode),
      dotQ (fun k => register b mode (i+1) k - register b mode i k) (billHistory b mode i) =
        charge b mode i := by
  cases b <;> cases mode <;> intro i <;> fin_cases i <;> decide +kernel

private theorem bill_exact (b : Band) (mode : Bool) :
    weightedBill (billCount b mode) (tariffWeights b mode) (billHistory b mode) = credit b mode := by
  unfold weightedBill
  trans (∑ i ∈ range (billCount b mode), charge b mode i)
  · apply sum_congr rfl
    intro i hi
    have h : i < billCount b mode := mem_range.mp hi
    simp only [register_eq b mode i (by omega : i ≤ billCount b mode),
      register_eq b mode (i+1) (by omega : i+1 ≤ billCount b mode)]
    exact charge_eq b mode ⟨i,h⟩
  · cases b <;> cases mode <;> decide +kernel


theorem loss_ledger (b : Band) : LossLedger b := by
  have seed : seedLimit b = credit b false :=
    (seed_bill_eq b (tariffWeights b false)).trans (bill_exact b false)
  refine ⟨?_,?_,?_,?_,?_⟩
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
    · have heq : weightedBill (lossCount b) (lossWeights b (rate0 b) (rate1 b)) (lossHistory b) =
          weightedBill (lossCount b) (lossWeights b (rate0 b) (rate1 b)) (billHistory b true) := by
        unfold weightedBill
        exact sum_congr rfl fun i hi => by rw [billHistory_eq b i (mem_range.mp hi)]
      have cost := heq.trans (bill_exact b true)
      rw [cost,seed]
      cases b <;> try (simp [start] at hb) <;> decide +kernel
  · intro hj
    cases b <;> simp only [jointRank, Bool.false_eq_true] at hj
    decide +kernel
  · intro hb
    rw [seed]
    cases b <;> try (simp [start] at hb) <;> decide +kernel

#print axioms schedule
#print axioms loss_ledger
end HighCore82258
