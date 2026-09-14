import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811B

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 280
def denominator : ℕ := 3936699200
def g0 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    224287811830250*a +
    70095140289360*b +
    565490446511860
def identitySlack0 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    10484210439771552610*a +
    3519687279349633680*b +
    26450088151548049580
def helperSlack0 (a b c : ℕ) : ℕ :=
    67325125073166884560*a^3 +
    202282468817120615280*a^2*b +
    202589562414740576880*a^2*c +
    31441540862431507205992*a^2 +
    202589562414740576880*a*b^2 +
    405486218427101115360*a*b*c +
    68393552772366757112784*a*b +
    6928049989588199478804*a*c +
    276103771357815574905120*a +
    1188327758381205990083*b^2 +
    2385434763631057433926*b*c +
    184998880369838160926604*b +
    19237836685774382079784*c +
    508110516948174678958324
def g1 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2210412046659320*a +
    70095140289360*b +
    70713629735784*c +
    5199795480332560
def identitySlack1 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    109435513187582853880*a +
    3519687279349633680*b +
    3550743489922921992*c +
    257207563175634882080
def helperSlack1 (a b c : ℕ) : ℕ :=
    67195822505747953360*a^3 +
    202023863682282752880*a^2*b +
    202460259847321645680*a^2*c +
    31438960492761300037992*a^2 +
    202460259847321645680*a*b^2 +
    405356915859682184160*a*b*c +
    68390557556959414207184*a*b +
    6926676149644955363604*a*c +
    276089605871724957997920*a +
    1187912912644070252483*b^2 +
    2385019917893921696326*b*c +
    184992328403757056376204*b +
    19234903133190326055784*c +
    508088072867608664191924
def g2 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2210412046659320*a +
    4810363370400*b^2 +
    9620726740800*b*c +
    2604183660882600*b +
    220319171215696*c +
    8570614249257280
def identitySlack2 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    109435513187582853880*a +
    241542775917895200*b^2 +
    483085551835790400*b*c +
    129207967252576412520*b +
    10284933088592952608*c +
    424132619717400917840
def helperSlack2 (a b c : ℕ) : ℕ :=
    67115008401111121360*a^3 +
    201862235473009088880*a^2*b +
    202379445742684813680*a^2*c +
    31438297327446903333992*a^2 +
    202379445742684813680*a*b^2 +
    405276101755045352160*a*b*c +
    68389633092706691746384*a*b +
    6925951516403950538004*a*c +
    276088114951680912319520*a +
    1187651613705744495683*b^2 +
    2384758618955595939526*b*c +
    184990829963776233393804*b +
    19233433663017739225384*c +
    508087102638766326919924
def conductor (a b c : ℕ) : ℕ :=
    241413776190160*a^3 +
    724241328570480*a^2*b +
    724241328570480*a^2*c +
    50765666883089192*a^2 +
    724241328570480*a*b^2 +
    1448482657140960*a*b*c +
    101531333766178384*a*b +
    13011586140942564*a*c +
    489550635616629920*a +
    2896300401318083*b^2 +
    5792600802636166*b*c +
    300970135003827404*b +
    35410892128119944*c +
    1021173382521647924
def slope (a b : ℕ) : ℕ :=
    202896656012360538480*a^2 +
    405793312024721076960*a*b +
    6931182883435113347604*a +
    2386423389511114678726*b +
    19244454015439947428584
def intercept (a b : ℕ) : ℕ :=
    67632218670786846160*a^3 +
    202896656012360538480*a^2*b +
    31458979174342173868392*a^2 +
    202896656012360538480*a*b^2 +
    68411979710157481019984*a*b +
    276225066293645994394720*a +
    1189316384261263234883*b^2 +
    185045568219186927443404*b +
    508319348536724395196724
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 8 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source11,source13,source14,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 280
def denominator : ℕ := 3936699200
def g0 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    227895666934390*a +
    72156771777440*b +
    576657686540460
def identitySlack0 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    10665371668115734430*a +
    3623207981260594720*b +
    27010828775104141380
def helperSlack0 (a b c : ℕ) : ℕ :=
    67325125073166884560*a^3 +
    202282468817120615280*a^2*b +
    202589562414740576880*a^2*c +
    30450921919780051961046*a^2 +
    202589562414740576880*a*b^2 +
    405486218427101115360*a*b*c +
    64359444312380094070492*a*b +
    6999140733673750507948*a*c +
    264780582837668146916860*a +
    1217335123937818646033*b^2 +
    2414442147781310499426*b*c +
    173653056214338156840728*b +
    19455970567071661111816*c +
    484453494858289011656258
def g1 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2140058872128590*a +
    72156771777440*b +
    70713629735784*c +
    5038386420282460
def identitySlack1 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    105902869234871308390*a +
    3623207981260594720*b +
    3550743489922921992*c +
    249102730043339210780
def helperSlack1 (a b c : ℕ) : ℕ :=
    67179659684820586960*a^3 +
    201991538040428020080*a^2*b +
    202444097026394279280*a^2*c +
    30448715352102689599446*a^2 +
    202444097026394279280*a*b^2 +
    405340753038754817760*a*b*c +
    64356771716699325977692*a*b +
    6997613346911144165548*a*c +
    264770045955321038507260*a +
    1216869095934412914833*b^2 +
    2413976119777904768226*b*c +
    173647605132363441243928*b +
    19452721839407588580616*c +
    484437830938366775649858
def g2 (a b c : ℕ) : ℕ :=
    4810363370400*a^2 +
    9620726740800*a*b +
    9620726740800*a*c +
    2140058872128590*a +
    4810363370400*b^2 +
    9620726740800*b*c +
    2387712354634200*b +
    221762313257352*c +
    8117823492923980
def identitySlack2 (a b c : ℕ) : ℕ :=
    241542775917895200*a^2 +
    483085551835790400*a*b +
    483085551835790400*a*c +
    105902869234871308390*a +
    241542775917895200*b^2 +
    483085551835790400*b*c +
    118338293551925503320*b +
    10357397579930625336*c +
    401396637469636924940
def helperSlack2 (a b c : ℕ) : ℕ :=
    67098845580183754960*a^3 +
    201829909831154356080*a^2*b +
    202363282921757447280*a^2*c +
    30447351797881440351446*a^2 +
    202363282921757447280*a*b^2 +
    405259938934117985760*a*b*c +
    64355146863539750972892*a*b +
    6996899488884090917548*a*c +
    264763127656563857619260*a +
    1216607796996087158033*b^2 +
    2413714820839579011426*b*c +
    173644180622888773765528*b +
    19451282001073368588616*c +
    484427232268000131917058
def conductor (a b c : ℕ) : ℕ :=
    241413776190160*a^3 +
    724241328570480*a^2*b +
    724241328570480*a^2*c +
    48334086026712646*a^2 +
    724241328570480*a*b^2 +
    1448482657140960*a*b*c +
    96668172053425292*a*b +
    13127663111655068*a*c +
    465234827052864460*a +
    2914894041727633*b^2 +
    5829788083455266*b*c +
    286455024427206328*b +
    35833497601895656*c +
    970184559099378658
def slope (a b : ℕ) : ℕ :=
    202896656012360538480*a^2 +
    405793312024721076960*a*b +
    7002279015127640165548*a +
    2415430773661367744226*b +
    19462602712656409879816
def intercept (a b : ℕ) : ℕ :=
    67632218670786846160*a^3 +
    202896656012360538480*a^2*b +
    30467837633814067109846*a^2 +
    202896656012360538480*a*b^2 +
    64377348652294166464092*a*b +
    264897827957283167236860*a +
    1218323749817875890833*b^2 +
    173698306919526131695128*b +
    484655141678020719765058
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 9 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source15,source16,source17,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 72
def denominator : ℕ := 260304192
def g0 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    56900896948320*a +
    18090731372238*b +
    143696252636124
def identitySlack0 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    2657119564153217424*a +
    908389894394186694*b +
    6715306997835757572
def helperSlack0 (a b c : ℕ) : ℕ :=
    4448493751338584208*a^3 +
    13368993210662746032*a^2*b +
    13392505167309739440*a^2*c +
    2077652902155651289679*a^2 +
    13392505167309739440*a*b^2 +
    26808522291266472288*a*b*c +
    4363725187851561505414*a*b +
    451727307813786965616*a*c +
    18037353230684555936054*a +
    78812018530818241634*b^2 +
    155955195251328624244*b*c +
    11758538421599337326186*b +
    1251131777683706570504*c +
    32954122485704626929875
def g1 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    2473901161920*a*c +
    567979342843352*a +
    18090731372238*b +
    17626864287420*c +
    1336216525514444
def identitySlack1 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    124221999043488960*a*c +
    28119856393567684504*a +
    908389894394186694*b +
    885097736464220460*c +
    66095214524092902892
def helperSlack1 (a b c : ℕ) : ℕ :=
    4438875223619359632*a^3 +
    13349756155224296880*a^2*b +
    13382886639590514864*a^2*c +
    2077522316892982164047*a^2 +
    13382886639590514864*a*b^2 +
    26798903763547247712*a*b*c +
    4363563787676014123270*a*b +
    451626313260504423792*a*c +
    18036775223817351990710*a +
    78781203617939985122*b^2 +
    155924380338450367732*b*c +
    11758220108298573151274*b +
    1250916963854490345992*c +
    32953297376991364350419
def g2 (a b c : ℕ) : ℕ :=
    1236950580960*a^2 +
    2473901161920*a*b +
    2473901161920*a*c +
    567979342843352*a +
    1236950580960*b^2 +
    2473901161920*b*c +
    626143121200809*b +
    55663918055472*c +
    2144903778097922
def identitySlack2 (a b c : ℕ) : ℕ :=
    62110999521744480*a^2 +
    124221999043488960*a*b +
    124221999043488960*a*c +
    28119856393567684504*a +
    62110999521744480*b^2 +
    124221999043488960*b*c +
    31040434196230672845*b +
    2595007143006640800*c +
    106101690488916844666
def helperSlack2 (a b c : ℕ) : ℕ :=
    4433531597108679312*a^3 +
    13339068902202936240*a^2*b +
    13377543013079834544*a^2*c +
    2077433936557393597007*a^2 +
    13377543013079834544*a*b^2 +
    26793560137036567392*a*b*c +
    4363458485856475068550*a*b +
    451580536186601438064*a*c +
    18036332459071123221878*a +
    78764282133989497442*b^2 +
    155907458854499880052*b*c +
    11758001173472485508714*b +
    1250826478421794274120*c +
    32952625360985535117203
def conductor (a b c : ℕ) : ℕ :=
    13742419975056*a^3 +
    41227259925168*a^2*b +
    41227259925168*a^2*c +
    2752199083905935*a^2 +
    41227259925168*a*b^2 +
    82454519850336*a*b*c +
    5504398167811870*a*b +
    736258184826096*a*c +
    26491309340930150*a +
    163798389701810*b^2 +
    327596779403620*b*c +
    16302615603814322*b +
    1998195654857000*c +
    55235648046668771
def slope (a b : ℕ) : ℕ :=
    13416017123956732848*a^2 +
    26832034247913465696*a*b +
    451967771036664807024*a +
    156030718506012906100*b +
    1251639689490225476744
def intercept (a b : ℕ) : ℕ :=
    4472005707985577616*a^3 +
    13416017123956732848*a^2*b +
    2078969785436262466895*a^2 +
    13416017123956732848*a*b^2 +
    4365117594386856964486*a*b +
    18046498184864065711670*a +
    78887541785502523490*b^2 +
    11762061573203071218602*b +
    32969858566443138070355
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 10 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source18,source19,source20,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 120
def denominator : ℕ := 723067200
def g0 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    92567033610312*a +
    28991551241685*b +
    232655969063610
def identitySlack0 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    4314659834819971896*a +
    1455752762498728905*b +
    10848832614954487530
def helperSlack0 (a b c : ℕ) : ℕ :=
    12356926033992620880*a^3 +
    37136089092663955440*a^2*b +
    37201400083350048240*a^2*c +
    5947575925892906236421*a^2 +
    37201400083350048240*a*b^2 +
    74468111157386189280*a*b*c +
    13103689967429223440002*a*b +
    1228722645169162718886*a*c +
    52471641509719642325810*a +
    211938567466493127229*b^2 +
    423119531317487921858*b*c +
    35468792218177005188362*b +
    3390727158257487304774*c +
    96802934965621420617997
def g1 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    975769963103784*a +
    28991551241685*b +
    28862699273680*c +
    2293469542686330
def identitySlack1 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    48329519909621056872*a +
    1455752762498728905*b +
    1449282718629293840*c +
    113494943027635565490
def helperSlack1 (a b c : ℕ) : ℕ :=
    12336145264228864080*a^3 +
    37094527553136441840*a^2*b +
    37180619313586291440*a^2*c +
    5947324253711079081221*a^2 +
    37180619313586291440*a*b^2 +
    74447330387622432480*a*b*c +
    13103369520795082899202*a*b +
    1228493561895104606886*a*c +
    52470623176213937962610*a +
    211869793014179741629*b^2 +
    423050756865174536258*b*c +
    35468172186698102996362*b +
    3390228172294893443974*c +
    96801544171664762568397
def g2 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    975769963103784*a +
    2061584301600*b^2 +
    4123168603200*b*c +
    1177320211457205*b +
    90711565271040*c +
    3821161722311610
def identitySlack2 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    48329519909621056872*a +
    103518332536240800*b^2 +
    207036665072481600*b*c +
    58449962530191385545*b +
    4221491203100106960*c +
    189204722027909351730
def helperSlack2 (a b c : ℕ) : ℕ :=
    12306458450280640080*a^3 +
    37035153925239993840*a^2*b +
    37150932499638067440*a^2*c +
    5946813460637399337221*a^2 +
    37150932499638067440*a*b^2 +
    74417643573674208480*a*b*c +
    13102764719477233779202*a*b +
    1228220443169031922086*a*c +
    52468008879267607407410*a +
    211775784770010365629*b^2 +
    422956748621005160258*b*c +
    35466901456283155460362*b +
    3389673770912288776774*c +
    96797535287496648950797
def conductor (a b c : ℕ) : ℕ :=
    37120329817680*a^3 +
    111360989453040*a^2*b +
    111360989453040*a^2*c +
    8270315330438981*a^2 +
    111360989453040*a*b^2 +
    222721978906080*a*b*c +
    16540630660877962*a*b +
    1955226250779366*a*c +
    79919128568063810*a +
    437902432845829*b^2 +
    875804865691658*b*c +
    49034920935503362*b +
    5278707705207574*c +
    166742074493264797
def slope (a b : ℕ) : ℕ :=
    37266711074036141040*a^2 +
    74533422148072282080*a*b +
    1229385650763720907686*a +
    423328328575590430658*b +
    3392122191417379984774
def intercept (a b : ℕ) : ℕ :=
    12422237024678713680*a^3 +
    37266711074036141040*a^2*b +
    5951603041059137980421*a^2 +
    37266711074036141040*a*b^2 +
    13107925879853557692802*a*b +
    52499902213983709642610*a +
    212147364724595636029*b^2 +
    35479586559271429777162*b +
    96851709384829427457997
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 11 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source21,source22,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11


