import ProximityPrize.SubmissionLower.High6960High55ScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High6960High55

open Finset
open High6960High55_3
open K1_14 (Shape)

set_option maxHeartbeats 8000000

private def Fits (hi r : ℕ) (s : Shape) : Prop :=
  2 ≤ s.B ∧ 0 < s.J ∧ s.J ≤ s.B ∧ s.B < p ∧ s.U < p ∧
    0 < s.m*agreement ∧ 2*hi*r≤fullCutoff s

private instance (hi r : ℕ) (s : Shape) : Decidable (Fits hi r s) := by
  unfold Fits
  infer_instance

private theorem guard_of_fits {h r : ℕ} {s : Shape} (hf : Fits h r s) :
    BankGuard h r s :=
  ⟨⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩,hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.2.2.2.2.2.2⟩

private theorem checked_fits (b : Band) :
    (stages b).all (fun s => decide (Fits (finish b) s.reserve s.free.shape ∧
       Fits (finish b) s.reserve s.moving.shape))=true:=by
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
    obtain ⟨x,y⟩:=of_decide_eq_true (List.all_eq_true.mp (checked_fits b) _ (stage_mem hi))
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
  | .h2570 => [![6465,65343,315026,1454543],
    ![5001,65343,315026,1454543],
    ![(24326/9),(396458/9),(1833719/9),(9896216/9)],
    ![(7177/4),(477521/16),(1833719/9),824464],
    ![(32959/25),(110902/5),(1274091/8),824464],
    ![(4651/4),(52198/3),(2879328/25),(14846247/25)],
    ![(45508/49),(706863/49),94764,(1588198/3)],
    ![(6640/11),(1112974/121),(1715710/27),(27458564/81)],
    ![(102974/289),(1913794/289),(8794494/169),(27458564/81)],
    ![(102974/289),(2374807/361),(10696438/225),(3179089/16)],
    ![(58697/192),(554825/96),(15266964/361),(3179089/16)],
    ![(71797/256),(2579947/512),(3053108/81),(3179089/16)],
    ![(222162/1225),(2579947/512),(3053108/81),(3179089/16)],
    ![(63671/400),(2579947/512),(3053108/81),(3179089/16)],
    ![(63671/400),(40248227/8427),(58359467/1764),(243993847/1936)],
    ![(63671/400),(60101767/15210),(54760765/1922),(243993847/1936)],
    ![(63671/400),(8937799/2304),(80098507/2888),(243993847/1936)],
    ![(63671/400),(62307849/16384),(279303633/10609),(1436900850/11449)]]
  | .h8100 => [![132,1268,7340,32000],
    ![(175/3),401,(9439/2),(56625/4)],
    ![(463/9),(1975/6),(48059/16),(67505/8)],
    ![(2131/50),(7153/25),(127173/49),(53190/7)]]

private def receipt (b : Band) (i : ℕ) : Mass :=
  (historyTable b)[i]?.getD (fun _ => 0)

private theorem receipt_zero (b : Band) : history b 0 = receipt b 0 := by
  funext k
  cases b <;> fin_cases k <;> decide +kernel


private def selectorTable : Band → List (Fin 4 → ℕ)
  | .h2570 => [![1,1,1,1], ![1,1,1,1], ![1,1,1,1], ![1,1,2,2], ![1,1,2,2], ![1,1,2,2], ![1,1,3,3], ![1,1,5,5], ![1,1,5,4], ![2,2,7,6], ![2,2,9,9], ![3,3,13,14], ![4,4,14,14], ![4,3,14,12], ![5,5,21,18], ![7,6,26,23], ![9,9,34,30]]
  | .h8100 => [![1,1,2,2], ![1,1,3,3], ![2,2,5,5]]

private def selector (b : Band) (i : ℕ) (k : Fin 4) : ℕ :=
  ((selectorTable b)[i]?.getD (fun _ => 1)) k

private theorem foldl_le_entry (f : ℕ → ℚ) (xs : List ℕ) (a : ℚ) {j : ℕ}
    (hj:j ∈ xs):xs.foldl (fun z i => min z (f i)) a≤f j:=by
  have floor (v : ℚ) (zs : List ℕ) :
      zs.foldl (fun z i => min z (f i)) v≤v:=by
    induction zs generalizing v with
    | nil => exact le_rfl
    | cons i zs ih => exact (ih _).trans (min_le_left _ _)
  induction xs generalizing a with
  | nil => exact nomatch hj
  | cons i xs ih =>
    rcases List.mem_cons.mp hj with rfl | him
    · change xs.foldl (fun z k => min z (f k)) (min a (f j)) ≤ f j
      exact (floor _ _).trans (min_le_right _ _)
    · exact ih _ him

private theorem upper_corner (b : Band) (i r : ℕ) (k : Fin 4)
    (hp:0 < r) (hr:r≤(stageAt b i).reserve+1) :
    stageCap b i (decide (stopIndex b ≤ i)) k ≤
      cornerBound (stageAt b i).free.shape (stageAt b i).moving.shape r
        ((stageAt b i).reserve+1) (decide (stopIndex b≤ i)) k:=by
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hp.ne'
  change ((List.range ((stageAt b i).reserve + 1)).foldl
    (fun a j => min a (cornerBound (stageAt b i).free.shape (stageAt b i).moving.shape
      (j+1) ((stageAt b i).reserve+1) (decide (stopIndex b≤ i)) k))
    (cornerBound (stageAt b i).free.shape (stageAt b i).moving.shape
      1 ((stageAt b i).reserve+1) (decide (stopIndex b≤ i)) k))≤_
  exact foldl_le_entry _ _ _ (List.mem_range.mpr (by omega))

private theorem receipt_check (b : Band) :
    ∀ i : Fin (laterCount b), ∀ k : Fin 4,
      let r:=selector b i k
      let s:=stageAt b (i+1)
      0 < r ∧ r ≤ s.reserve+1 ∧ min (receipt b i k)
        (cornerBound s.free.shape s.moving.shape r (s.reserve+1) true k)≤receipt b (i+1) k:=by
  cases b <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem history_le (b : Band) (i : ℕ) (hi : i ≤ laterCount b) (k : Fin 4) :
    history b i k≤receipt b i k:=by
  induction i with
  | zero => exact (congrFun (receipt_zero b) k).le
  | succ i ih =>
    obtain ⟨hp,hr,hbound⟩:=receipt_check b ⟨i,by omega⟩ k
    have hcorner:=upper_corner b (i+1) (selector b i k) k hp hr
    change stageCap b (i+1) true k≤_ at hcorner
    rw [history]
    exact (min_le_min (ih (by omega)) hcorner).trans hbound

private def rate0Table : Band → List ℚ
  | .h2570 => [125538313,120739562,(1065353217/10),(710235478/7),(355117739/4),(1065353217/13),(2130706434/29),(2130706434/35),(1065353217/17),(355117739/6),(355117739/6),(355117739/5),(1065353217/14),(710235478/15),(651320621547851/9910152),(543017623468585/7795632),(1872121859984609/20793600),(17283444646616819/135795200)].map (fun c => (101/100:ℚ)*c)
  | .h8100 => []

private def rate0 (b : Band) (i : ℕ) : ℚ :=
  (rate0Table b)[i]?.getD 0

private def rate1Table : Band → List ℚ
  | .h2570 => [(1052826850693505106081184/325022951332417123),(1098257991573524261508352/325022951332417123),(3527027389837833/915254057),(77965865706932200/19220335197),(4269559180855387/915254057),(4640825076364164/915254057),(150733992286688104/26542367653),(220903254832873666/32033891995),(6125888658399272/915254057),(6497154553908049/915254057),(6497154553908049/915254057),(5383356867381718/915254057),(5012090971872941/915254057),(367553297383885096/41186432565),(854760868660857581681474662420/134209452133035675680529),(24352387044191735441342821255/4060511730995887117639),(7770453606626980722180940483717/1689599310206437172203200),(4397971272101393845472398447969/1379267396274245303162800)].map (fun c => (101/100:ℚ)*c)
  | .h8100 => []

private def rate1 (b : Band) (i : ℕ) : ℚ :=
  (rate1Table b)[i]?.getD 0

abbrev Q:ℚ:=((p+1:ℕ):ℚ)
private def alpha (hi:ℕ):ℚ:=1+2*((blockLength:ℚ) / agreement)*degreeAt hi
private def mu (hi:ℕ):ℚ:=((blockLength - degreeAt hi:ℕ):ℚ) / gap hi
private def drop (a:ℚ):=a / Q
private def quad (hi:ℕ) (a:ℚ):=2*alpha hi*drop a
private def slope (hi:ℕ) (a:ℚ):=2*alpha hi - (mu hi - alpha hi)*drop a
def raw (hi : ℕ) (a : ℚ) (g : ℕ) :=
  (1 - a*g / Q)*curveUnit hi g
private theorem raw_eq (hi : ℕ) (a : ℚ) (g : ℕ) :
    raw hi a g = -(quad hi a)*(g:ℚ)^2+slope hi a*g+(mu hi - alpha hi):=by
  unfold raw curveUnit quad slope drop mu alpha
  ring
private theorem raw_le_peak (hi : ℕ) (a : ℚ) (g m : ℕ) (hg : 0 < g)
    (hquad:0≤quad hi a)
    (hleft:m=1 ∨ quad hi a*(2*(m:ℚ) - 1)≤slope hi a)
    (hright:slope hi a≤quad hi a*(2*(m:ℚ)+1)) :
    raw hi a g≤raw hi a m:=by
  rw [raw_eq,raw_eq]
  rcases lt_trichotomy g m with h | rfl | h
  · have he : 0 ≤ (m : ℚ) - g := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : (g : ℚ) + m ≤ 2 * (m : ℚ) - 1 := by
      have hh:(g:ℚ)+1≤m:=by exact_mod_cast h
      linarith only [hh]
    have hb : quad hi a * ((g : ℚ) + m) ≤ slope hi a := by
      rcases hleft with hm | hm
      · omega
      · exact (mul_le_mul_of_nonneg_left hgm hquad).trans hm
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
  · exact le_rfl
  · have he : 0 ≤ (g : ℚ) - m := sub_nonneg.mpr (by exact_mod_cast h.le)
    have hgm : 2 * (m : ℚ) + 1 ≤ (g : ℚ) + m := by
      have hh:(m:ℚ)+1≤g:=by exact_mod_cast h
      linarith only [hh]
    have hb : slope hi a ≤ quad hi a * ((g : ℚ) + m) :=
      hright.trans (mul_le_mul_of_nonneg_left hgm hquad)
    nlinarith only [mul_nonneg he (sub_nonneg.mpr hb)]
def rateCheck (hi : ℕ) (a h : ℚ) (m : ℕ) : Bool :=
  decide (Q/81 ≤ a) && decide (0 ≤ h) && decide (0 ≤ quad hi a) &&
    (decide (m=1) || decide (quad hi a*(2*(m:ℚ) - 1)≤slope hi a)) &&
    decide (slope hi a≤quad hi a*(2*(m:ℚ)+1)) && decide (raw hi a m≤h)
theorem rate_of_check {hi : ℕ} {a h : ℚ} {m : ℕ}
    (hc:rateCheck hi a h m=true):RateOK hi a h:=by
  simp only [rateCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨ha,hh⟩,hquad⟩,hl⟩,hr⟩,hp⟩
  refine ⟨ha,hh,fun g hg _ => ?_⟩
  by_cases hz:0≤1 - a*g / Q
  · rw [max_eq_right hz]
    exact (raw_le_peak hi a g m hg hquad hl hr).trans hp
  · rw [max_eq_left (le_of_not_ge hz), zero_mul]
    exact hh

private def optimumTable : Band → List ℕ
  | .h2570 => [9,9,10,11,12,13,15,18,17,18,18,15,14,23,16,15,12,9]
  | .h8100 => []

private def optimum (b:Band) (i:ℕ):ℕ:=(optimumTable b)[i]?.getD 1

private theorem rate_valid (b : Band) (hb : start b < 7773) (i : Fin (laterCount b+1)) :
    RateOK (finish b) (rate0 b i) (rate1 b i):=by
  apply rate_of_check (m:=optimum b i)
  cases b <;> try (simp [start] at hb) <;> fin_cases i <;> decide +kernel

private def tariffCount (b : Band) (discount : Bool) : ℕ :=
  if discount then lossCount b else laterCount b+1

private def tariffWeights (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossWeights b (rate0 b) (rate1 b) else cutWeight b 0

private def tariffHistory (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount then lossHistory b else history b

private def tariffReceipt (b : Band) (discount : Bool) : ℕ → Mass :=
  if discount && jointRank b then
    High6960High55JointRank.splice (stopIndex b) (receipt b 0) (receipt b)
  else receipt b

private theorem tariff_history_le (b : Band) (discount : Bool) (i : ℕ)
    (hi:i < tariffCount b discount) (k:Fin 4) :
    tariffHistory b discount i k≤tariffReceipt b discount i k:=by
  cases discount with
  | false => exact history_le b i (Nat.le_of_lt_succ hi) k
  | true =>
    by_cases hj:jointRank b=true
    · have he : rankMass b = receipt b 0 := receipt_zero b
      have hlen : i < laterCount b + 2 := by
        simpa [tariffCount,lossCount,hj,Nat.add_assoc] using hi
      cases i with
      | zero =>
        simpa [tariffHistory, tariffReceipt, lossHistory, hj, stopIndex,
          High6960High55JointRank.splice,he]
      | succ i =>
        simpa [tariffHistory, tariffReceipt, lossHistory, hj, stopIndex,
          High6960High55JointRank.splice] using history_le b i (by omega) k
    · have hf : jointRank b = false := by cases e : jointRank b <;> simp_all
      have hi' : i < laterCount b+1 := by
        simpa [tariffCount,lossCount,hf] using hi
      simpa [tariffHistory, tariffReceipt, lossHistory, hf] using
        history_le b i (Nat.le_of_lt_succ hi') k

private theorem bill_le (b : Band) (mode : Bool) :
    weightedBill (tariffCount b mode) (tariffWeights b mode) (tariffHistory b mode) ≤
      weightedBill (tariffCount b mode) (tariffWeights b mode) (tariffReceipt b mode):=by
  unfold weightedBill
  apply sum_le_sum
  intro i hi
  exact P1_7_4.dotQ_mono_mass (fun k => sub_nonneg.mpr (le_max_left _ _))
    (tariff_history_le b mode i (mem_range.mp hi))

private def registerTable : Band → Bool → List Mass
  | .h2570, false => [![0,0,0,0],
    ![10666,379,101,0],
    ![11561,423,112,0],
    ![12709,452,120,0],
    ![13874,481,128,0],
    ![14099,573,153,0],
    ![14983,625,167,0],
    ![19042,764,204,0],
    ![25796,934,249,0],
    ![27241,1045,279,0],
    ![34056,1221,329,0],
    ![40812,1604,430,0],
    ![62059,1604,430,0],
    ![104847,1604,430,0],
    ![104847,2470,661,0],
    ![104847,3811,1019,0],
    ![105125,4575,1223,0],
    ![138831,6023,1607,0],
    ![234728,8288,2218,0]]
  | .h2570, true => [![0,0,0,0],
    ![1338991646458,(26693724895190416890446904665/325022951332417123),12679369613,(106335511920044015714199584/325022951332417123)],
    ![1395870076282,(29296804116138795196369470770/325022951332417123),13522830944,(123004895056234717288935424/325022951332417123)],
    ![1395870076282,(444490516490623907379/4576270285),13522830944,(423243286780539960/915254057)],
    ![1407686717396,(2019714658363333159778/19220335197),13522830944,(9979630810487321600/19220335197)],
    ![1407686717396,(427024210676995416731/3661016228),(54333014067/4),(653242554670874211/915254057)],
    ![1407686717396,(1513353301297417605381/11898302741),(177913987239/13),(775017787752815388/915254057)],
    ![1407686717396,(4360181890030914968200/26542367653),(434664112536/29),(30749734426484373216/26542367653)],
    ![(54963703171464/35),(7519848980935674645428/32033891995),(530545902066/35),(55004910453385542834/32033891995)],
    ![(29021286984297/17),(3855827612465855345989/15559318969),(297233547543/17),(1709122935693396888/915254057)],
    ![2015648286564,(574818532168078802549/1830508114),(116833736131/6),(2137563848235748121/915254057)],
    ![2415510860678,(1056154021930884420010/2745762171),(76350313885/3),(2793776458180461070/915254057)],
    ![(22038251764601/5),(2105634450998316714507/4576270285),(76350313885/3),(2793776458180461070/915254057)],
    ![(111699088742799/14),(4344490942175858400216/6406778399),(382461804903/14),(2793776458180461070/915254057)],
    ![(111699088742799/14),(4344490942175858400216/6406778399),(469465650958/15),(242952729570748048456/41186432565)],
    ![(111699088742799/14),(2586378536790134118573138008717376803/3221026851192856216332696),(663695713357260169/9910152),(871001325165413875733422681005980/134209452133035675680529)],
    ![(111699088742799/14),(801641410781340417815142572097786375/844586440047144520468912),(664110553502079455/7795632),(29782969355046492444762270394865/4060511730995887117639)],
    ![(86636183314507750693/6931200),(7980009910923593240010658867144479169/6758397240825748688812800),(3008499828995266663/20793600),(12487118945849558020544771357333219/1689599310206437172203200)],
    ![(507113549376384086279/16974400),(497452738702077330561185981928265463/275853479254849060632560),(19167340113098052271/67897600),(12487118945849558020544771357333219/1689599310206437172203200)]].map (fun c k => (101/100:ℚ)*c k)
  | .h8100, false => [![0,0,0,0],
    ![375,44,9,0],
    ![587,74,15,0],
    ![985,117,24,0],
    ![985,141,32,0]]
  | .h8100, true => [![0,0,0,0],
    ![0,0,0,0],
    ![0,0,0,0],
    ![0,0,0,0],
    ![0,0,0,0]]

private def chargeTable : Band → Bool → List ℚ
  | .h2570,false => [125538313,10816273,(18031094/3),(660352393/144),(252750487/40),(265879501/75),(454778061/49),(3085557770/363),(137295890296/48841),(5599070624126/938961),(296318778145/34656),(1525470859/256),(9505867656/1225),(90345025273/6912),(45211806449395/2477538),(2594614345537549/292336200),(56227485660223/2599200),(173662269033435817/4345446400)]
  | .h2570,true => [(6010754423597980961738592451547891/325022951332417123),(373154381986905947335446569790025/325022951332417123),(1951794490831464514466419611905026/4875344269986256845),(156516850851029591958483057/512542271920),(437057969048976814675836283/1025084543840),(489679874484034549147694297/1784745411150),(13921944885336877824924970525/16907488194961),(957641523922076463155994901988/1011662343094095),(1854141201432489992429815708826/6034759658721495),(12850233232616525689531971452775203/17531512438141450800),(176172705901690301191630967791/190314267596352),(6600422577155365254755013151/7029151157760),(8868478734454968321922517973961907/4882272665401152000),(44559344483272417916659055621/62273886038280),(17873691836972776339298641006612491264332049533713/9656061871649282391445574728762080),(1113230180232120069073514517102717173132972105815629571/925214455468331364746297209296557222640),(63314076345322496359279043000115303820198197428070218449/19331560048507675319338391406470307840000),(303134653673228433970452103716605062756953619291705591/34618643961305642435036750919761920000)].map (fun c => (101/100:ℚ)*c)
  | .h8100,false => [171352,(158141/3),(8879363/144),(33846528/1225)]
  | .h8100,true => [0,0,0,0]

private def credit : Band → Bool → ℚ
  | .h2570,false => (10178735088520014669698391849937012099/33109032338729008715121868800)
  | .h2570,true => (101/100:ℚ)*(1133873348190005211048130620314331473005660605125992911532910189549740188771852523205873/26161912156642214734503138967942620012153998780735985128052078673920000)
  | .h8100,false => (55276303307/176400)
  | .h8100,true => 0

private def register (b : Band) (mode : Bool) (i : ℕ) : Mass :=
  (registerTable b mode)[i]?.getD (fun _ => 0)

private def charge (b : Band) (mode : Bool) (i : ℕ) : ℚ :=
  (chargeTable b mode)[i]?.getD 0

private theorem register_step (b : Band) (mode : Bool) :
    ∀ i : Fin (tariffCount b mode), ∀ k : Fin 4,
      max (register b mode i k) (tariffWeights b mode i k)=register b mode (i+1) k:=by
  cases b <;> cases mode <;> intro i k <;> fin_cases i <;> fin_cases k <;> decide +kernel

private theorem register_eq (b : Band) (mode : Bool) (i : ℕ) (hi : i ≤ tariffCount b mode) :
    running (tariffWeights b mode) i=register b mode i:=by
  induction i with
  | zero => funext k; cases b <;> cases mode <;> fin_cases k <;> decide +kernel
  | succ i ih =>
    funext k
    rw [running,ih (by omega:i≤tariffCount b mode)]
    exact register_step b mode ⟨i,by omega⟩ k

private theorem charge_eq (b : Band) (mode : Bool) :
    ∀ i : Fin (tariffCount b mode),
      dotQ (fun k => register b mode (i+1) k - register b mode i k) (tariffReceipt b mode i) =
        charge b mode i:=by
  cases b <;> cases mode <;> intro i <;> fin_cases i <;> decide +kernel

private theorem bill_exact (b : Band) (mode : Bool) :
    weightedBill (tariffCount b mode) (tariffWeights b mode) (tariffReceipt b mode)=credit b mode:=by
  unfold weightedBill
  trans (∑ i ∈ range (tariffCount b mode),charge b mode i)
  · apply sum_congr rfl
    intro i hi
    have h:i < tariffCount b mode:=mem_range.mp hi
    simp only [register_eq b mode i (by omega : i ≤ tariffCount b mode),
      register_eq b mode (i+1) (by omega:i+1≤tariffCount b mode)]
    exact charge_eq b mode ⟨i,h⟩
  · cases b <;> cases mode <;> decide +kernel

theorem loss_ledger (b : Band) : LossLedger b := by
  have seed : seedLimit b ≤ credit b false :=
    (bill_le b false).trans_eq (bill_exact b false)
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply seed.trans_lt
    cases b <;> decide +kernel
  · cases b <;> decide +kernel
  · intro hb
    refine ⟨rate0 b,rate1 b,?_,?_⟩
    · intro i hi
      refine ⟨rate_valid b hb ⟨i,by omega⟩, ?_⟩
      have hm : dotQ (cutWeight b 0 i) (history b i) ≤ dotQ (cutWeight b 0 i) (receipt b i) :=
        P1_7_4.dotQ_mono_mass (fun k => Nat.cast_nonneg _) (history_le b i hi)
      apply (min_le_min seed hm).trans
      have H : ∀ i : Fin (laterCount b+1),
          min (credit b false) (dotQ (cutWeight b 0 i) (receipt b i))≤rate0 b i:=by
        cases b <;> try (simp [start] at hb) <;> decide +kernel
      exact H ⟨i,by omega⟩
    · have cost : weightedBill (lossCount b) (lossWeights b (rate0 b) (rate1 b)) (lossHistory b) ≤
          credit b true:=(bill_le b true).trans_eq (bill_exact b true)
      apply (add_le_add (add_le_add cost seed) (le_refl (lossOffset b))).trans
      cases b <;> try (simp [start] at hb) <;> decide +kernel
  · intro hj
    cases b <;> try (simp [jointRank] at hj) <;> decide +kernel
  · intro hb
    apply (mul_le_mul_of_nonneg_left seed (by positivity:0≤((p+1:ℕ):ℚ))).trans
    cases b <;> try (simp [start] at hb) <;> decide +kernel

#print axioms schedule
#print axioms loss_ledger
end High6960High55
