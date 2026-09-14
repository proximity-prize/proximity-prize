import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811A

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 72
def denominator : ℕ := 260304192
def g0 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    54633102311432*a +
    17394930745011*b +
    137476966189814
def identitySlack0 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    2543246792051160280*a +
    873451657499237343*b +
    6403017967507193542
def helperSlack0 (a b c : ℕ) : ℕ :=
    4449562476640720272*a^3 +
    13371130661267018160*a^2*b +
    13393573892611875504*a^2*c +
    2376807049833046710981*a^2 +
    13393573892611875504*a*b^2 +
    26809591016568608352*a*b*c +
    4953007339674216423618*a*b +
    443526142154307570310*a*c +
    20618052075121605180594*a +
    76296997457705165933*b^2 +
    151204124637610999618*b*c +
    13318650810377709225866*b +
    1224154971686967584294*c +
    37598503795230142669517
def g1 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    2473901161920*a*c +
    650650765515360*a +
    17394930745011*b +
    17008374840996*c +
    1528189394141094
def identitySlack1 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    124221999043488960*a*c +
    32271036540197222208*a +
    873451657499237343*b +
    854041525890932148*c +
    75734748176442879342
def helperSlack1 (a b c : ℕ) : ℕ :=
    4441012674223631760*a^3 +
    13354031056432841136*a^2*b +
    13385024090194786992*a^2*c +
    2376700909231075493829*a^2 +
    13385024090194786992*a*b^2 +
    26801041214151519840*a*b*c +
    4952873412214389668802*a*b +
    443437081701591179398*a*c +
    20617614440450114283186*a +
    76269210599849628269*b^2 +
    151176337779755461954*b*c +
    13318392293871878386250*b +
    1223965094785544762534*c +
    37597902600630850293581
def g2 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    2473901161920*a*c +
    650650765515360*a +
    1236950580960*b^2 +
    2473901161920*b*c +
    706392126874323*b +
    55663918055472*c +
    2444804701916262
def identitySlack2 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    124221999043488960*a*c +
    32271036540197222208*a +
    62110999521744480*b^2 +
    124221999043488960*b*c +
    35069977518114831327*b +
    2595007143006640800*c +
    121160615576607151086
def helperSlack2 (a b c : ℕ) : ℕ :=
    4435669047712951440*a^3 +
    13343343803411480496*a^2*b +
    13379680463684106672*a^2*c +
    2376592935598281098949*a^2 +
    13379680463684106672*a*b^2 +
    26795697587640839520*a*b*c +
    4952748517097644786242*a*b +
    443391304627688193670*a*c +
    20617019827613168814834*a +
    76252289115899140589*b^2 +
    151159416295804974274*b*c +
    13318119477478474717130*b +
    1223874609352848690662*c +
    37596961176676326326285
def conductor (a b c : ℕ) : ℕ :=
    13742419975056*a^3 +
    41227259925168*a^2*b +
    41227259925168*a^2*c +
    3102806032924101*a^2 +
    41227259925168*a*b^2 +
    82454519850336*a*b*c +
    6205612065848202*a*b +
    725760182541766*a*c +
    29997378831111810*a +
    161419061911349*b^2 +
    322838123822698*b*c +
    18396739986761474*b +
    1957184336842166*c +
    62588876664888413
def slope (a b : ℕ) : ℕ :=
    13416017123956732848*a^2 +
    26832034247913465696*a*b +
    443758233694293047686*a +
    151276263595505183938*b +
    1224646941669639917222
def intercept (a b : ℕ) : ℕ :=
    4472005707985577616*a^3 +
    13416017123956732848*a^2*b +
    2378241272676376697541*a^2 +
    13416017123956732848*a*b^2 +
    4954513701475440594498*a*b +
    20628154894047232087986*a +
    76369136415599350253*b^2 +
    13322501467998276027338*b +
    37615962077370129653837
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 4 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source4,source5,source6,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
#print axioms retained_cap
#print axioms identity_absorption
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 126
def denominator : ℕ := 797181588
def g0 (a b c : ℕ) : ℕ :=
    2164663516680*a^2 +
    4329327033360*a*b +
    99215784149146*a +
    30615078960576*b +
    249234984014932
def identitySlack0 (a b c : ℕ) : ℕ :=
    108694249163052840*a^2 +
    217388498326105680*a*b +
    4631843114433712310*a +
    1537274959847402688*b +
    11639638614723391046
def helperSlack0 (a b c : ℕ) : ℕ :=
    13626786950601124860*a^3 +
    40949093247797000196*a^2*b +
    41017825643790625812*a^2*c +
    6408562211750712726666*a^2 +
    41017825643790625812*a*b^2 +
    82104383683574877240*a*b*c +
    14613296477142516429924*a*b +
    1377683841977191170992*a*c +
    57179635147724949387072*a +
    234755772260032257203*b^2 +
    471006770725173616564*b*c +
    39706115738257469752496*b +
    3807070079518431590036*c +
    106252495895890209402350
def g1 (a b c : ℕ) : ℕ :=
    2164663516680*a^2 +
    4329327033360*a*b +
    4329327033360*a*c +
    1001179560184146*a +
    30615078960576*b +
    30847012502985*c +
    2353824009364932
def identitySlack1 (a b c : ℕ) : ℕ :=
    108694249163052840*a^2 +
    217388498326105680*a*b +
    217388498326105680*a*c +
    49572071145431811522*a +
    1537274959847402688*b +
    1548921038812385805*c +
    116442169707004551576
def helperSlack1 (a b c : ℕ) : ℕ :=
    13610422094412166380*a^3 +
    40916363535419083236*a^2*b +
    41001460787601667332*a^2*c +
    6408355915407315976794*a^2 +
    41001460787601667332*a*b^2 +
    82088018827385918760*a*b*c +
    14613039449744933908764*a*b +
    1377514192947223151936*a*c +
    57178778750464756651272*a +
    234705041205846485915*b^2 +
    470956039670987845276*b*c +
    39705630237692573795144*b +
    3806714416573173784172*c +
    106251330094458476355206
def g2 (a b c : ℕ) : ℕ :=
    2164663516680*a^2 +
    4329327033360*a*b +
    4329327033360*a*c +
    1001179560184146*a +
    2164663516680*b^2 +
    4329327033360*b*c +
    1285993950262398*b +
    96870678331455*c +
    4024080178518816
def identitySlack2 (a b c : ℕ) : ℕ :=
    108694249163052840*a^2 +
    217388498326105680*a*b +
    217388498326105680*a*c +
    49572071145431811522*a +
    108694249163052840*b^2 +
    217388498326105680*b*c +
    63873456114431079198*b +
    4514088316009994127*c +
    199260502892715610548
def helperSlack2 (a b c : ℕ) : ℕ :=
    13577692382034249420*a^3 +
    40850904110663249316*a^2*b +
    40968731075223750372*a^2*c +
    6407907320036906768394*a^2 +
    40968731075223750372*a*b^2 +
    82055289115008001800*a*b*c +
    14612487210285327963324*a*b +
    1377210897570902822480*a*c +
    57176784152826373506708*a +
    234601397116649748875*b^2 +
    470852395581791108236*b*c +
    39704544280891731587444*b +
    3806097188601582853808*c +
    106248485030961404230514
def conductor (a b c : ℕ) : ℕ :=
    43952050092636*a^3 +
    131856150277908*a^2*b +
    131856150277908*a^2*c +
    9316384352005950*a^2 +
    131856150277908*a*b^2 +
    263712300555816*a*b*c +
    18632768704011900*a*b +
    2342561122953866*a*c +
    89867439763111800*a +
    521391146774411*b^2 +
    1042782293548822*b*c +
    55214891543297276*b +
    6344268800123174*c +
    187444856257545770
def slope (a b : ℕ) : ℕ :=
    41086558039784251428*a^2 +
    82173116079568502856*a*b +
    1378395713308809292688*a +
    471229878264549750508*b +
    3808584647275018769456
def intercept (a b : ℕ) : ℕ :=
    13695519346594750476*a^3 +
    41086558039784251428*a^2*b +
    6412631586046282029834*a^2 +
    41086558039784251428*a*b^2 +
    14617588958977461867036*a*b +
    57208077271984151820852*a +
    234978879799408391147*b^2 +
    39717036259315708529348*b +
    106301546550656515291634
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 5 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source7,source8,source9,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
#print axioms retained_cap
#print axioms identity_absorption
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 9
def denominator : ℕ := 4067253
def g0 (a b c : ℕ) : ℕ :=
    154618822620*a^2 +
    309237645240*a*b +
    6932219363333*a +
    2242013626329*b +
    17515342987628
def identitySlack0 (a b c : ℕ) : ℕ :=
    7763874940218060*a^2 +
    15527749880436120*a*b +
    323081884101943087*a +
    112578230218858077*b +
    816983800465022659
def helperSlack0 (a b c : ℕ) : ℕ :=
    69340689514601082*a^3 +
    208556431194871278*a^2*b +
    209090793845939310*a^2*c +
    36984610414131628656*a^2 +
    209090793845939310*a*b^2 +
    418715950342946652*a*b*c +
    73937091058573564896*a*b +
    6963866072125634328*a*c +
    316642721319057434259*a +
    1222285302997294338*b^2 +
    2445116101200887292*b*c +
    197949450800121396309*b +
    19345112281312970913*c +
    572589188171353054701
def g1 (a b c : ℕ) : ℕ :=
    154618822620*a^2 +
    309237645240*a*b +
    309237645240*a*c +
    80996330572607*a +
    2242013626329*b +
    2242013626329*c +
    190332167526368
def identitySlack1 (a b c : ℕ) : ℕ :=
    7763874940218060*a^2 +
    15527749880436120*a*b +
    15527749880436120*a*c +
    4017057453464121607*a +
    112578230218858077*b +
    112578230218858077*c +
    9432120894056032174
def helperSlack1 (a b c : ℕ) : ℕ :=
    69340689514601082*a^3 +
    208556431194871278*a^2*b +
    209090793845939310*a^2*c +
    36984610414131628656*a^2 +
    209090793845939310*a*b^2 +
    418715950342946652*a*b*c +
    73937091058573564896*a*b +
    6963866072125634328*a*c +
    316642721319057434259*a +
    1222285302997294338*b^2 +
    2445116101200887292*b*c +
    197949450800121396309*b +
    19345112281312970913*c +
    572589188171353054701
def g2 (a b c : ℕ) : ℕ :=
    154618822620*a^2 +
    309237645240*a*b +
    309237645240*a*c +
    80996330572607*a +
    154618822620*b^2 +
    309237645240*b*c +
    80996330572607*b +
    6932219363333*c +
    295081820958524
def identitySlack2 (a b c : ℕ) : ℕ :=
    7763874940218060*a^2 +
    15527749880436120*a*b +
    15527749880436120*a*c +
    4017057453464121607*a +
    7763874940218060*b^2 +
    15527749880436120*b*c +
    4017057453464121607*b +
    323081884101943087*c +
    14616898110701101522
def helperSlack2 (a b c : ℕ) : ℕ :=
    69340689514601082*a^3 +
    208556431194871278*a^2*b +
    209090793845939310*a^2*c +
    36984610414131628656*a^2 +
    209090793845939310*a*b^2 +
    418715950342946652*a*b*c +
    73937091058573564896*a*b +
    6963866072125634328*a*c +
    316642721319057434259*a +
    1222285302997294338*b^2 +
    2445116101200887292*b*c +
    197949450800121396309*b +
    19345112281312970913*c +
    572589188171353054701
def conductor (a b c : ℕ) : ℕ :=
    177703706574*a^3 +
    533111119722*a^2*b +
    533111119722*a^2*c +
    33043957584537*a^2 +
    533111119722*a*b^2 +
    1066222239444*a*b*c +
    66087915169074*a*b +
    9339466457166*a*c +
    317111797852320*a +
    2102847982641*b^2 +
    4205695965282*b*c +
    195479803923624*b +
    25234457787900*c +
    660751833867525
def slope (a b : ℕ) : ℕ :=
    209625156497007342*a^2 +
    419250312994014684*a*b +
    6969376687644255840*a +
    2446847213539243104*b +
    19356813990882225423
def intercept (a b : ℕ) : ℕ :=
    69875052165669114*a^3 +
    209625156497007342*a^2*b +
    37009919063154134388*a^2 +
    209625156497007342*a*b^2 +
    73964130819934426440*a*b +
    316814787884533269927*a +
    1224016415335650150*b^2 +
    198016923266167822074*b +
    572883469139982371535
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 6 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source10,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source10,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
#print axioms retained_cap
#print axioms identity_absorption
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 280
def denominator : ℕ := 3936699200
def g0 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    224287811830250*a +
    71125956033400*b +
    566864888475460
def identitySlack0 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    10484210439771552610*a +
    3571447630305114200*b +
    26519103005866296380
def helperSlack0 (a b c : ℕ) : ℕ :=
    67325125073166884560*a^3 +
    202282468817120615280*a^2*b +
    202589562414740576880*a^2*c +
    31441071703591791210792*a^2 +
    202589562414740576880*a*b^2 +
    405486218427101115360*a*b*c +
    67190178007895827251984*a*b +
    6928028386505739411604*a*c +
    274496240027058082863520*a +
    1202826049521172015683*b^2 +
    2399933060036479150726*b*c +
    181437206449358729070604*b +
    19257113566530881183784*c +
    503331052966766498140724
def g1 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2210412046659320*a +
    71125956033400*b +
    70713629735784*c +
    5201169922296160
def identitySlack1 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    109435513187582853880*a +
    3571447630305114200*b +
    3550743489922921992*c +
    257276578029953128880
def helperSlack1 (a b c : ℕ) : ℕ :=
    67195822505747953360*a^3 +
    202023863682282752880*a^2*b +
    202460259847321645680*a^2*c +
    31438960055728477668392*a^2 +
    202460259847321645680*a*b^2 +
    405356915859682184160*a*b*c +
    67187646126688402183184*a*b +
    6926676096990398451604*a*c +
    274485696287040678669920*a +
    1202405816177060489283*b^2 +
    2399512826692367624326*b*c +
    181431904089750021264204*b +
    19254227155497587188584*c +
    503314996386331268507124
def g2 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2210412046659320*a +
    4810363370400*b^2 +
    9620726740800*b*c +
    2518625954127280*b +
    220319171215696*c +
    8456535566278480
def identitySlack2 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    109435513187582853880*a +
    241542775917895200*b^2 +
    483085551835790400*b*c +
    124911858123271529360*b +
    10284933088592952608*c +
    418404386808986433440
def helperSlack2 (a b c : ℕ) : ℕ :=
    67115008401111121360*a^3 +
    201862235473009088880*a^2*b +
    202379445742684813680*a^2*c +
    31437828168607187338792*a^2 +
    202379445742684813680*a*b^2 +
    405276101755045352160*a*b*c +
    67186258328235761885584*a*b +
    6925929913321490470804*a*c +
    274480583620923420277920*a +
    1202149904845710521283*b^2 +
    2399256915361017656326*b*c +
    181429156043296801537804*b +
    19252710543774238329384*c +
    503307638657358146102324
def conductor (a b c : ℕ) : ℕ :=
    241413776190160*a^3 +
    724241328570480*a^2*b +
    724241328570480*a^2*c +
    50328634060719592*a^2 +
    724241328570480*a*b^2 +
    1448482657140960*a*b*c +
    100657268121439184*a*b +
    12958931584030564*a*c +
    485180307392933920*a +
    2901565857009283*b^2 +
    5803131714018566*b*c +
    298368999892374604*b +
    35273990280148744*c +
    1012016755074651124
def slope (a b : ℕ) : ℕ :=
    202896656012360538480*a^2 +
    405793312024721076960*a*b +
    6931161280352653280404*a +
    2400921685916536395526*b +
    19263730896196446532584
def intercept (a b : ℕ) : ℕ :=
    67632218670786846160*a^3 +
    202896656012360538480*a^2*b +
    31458510015502457873192*a^2 +
    202896656012360538480*a*b^2 +
    67208604945686551159184*a*b +
    274617534962888502353120*a +
    1203814675401229260483*b^2 +
    181483894298707495587404*b +
    503539884555316214379124
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 7 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source11,source12,source13,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith
#print axioms retained_cap
#print axioms identity_absorption
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7


