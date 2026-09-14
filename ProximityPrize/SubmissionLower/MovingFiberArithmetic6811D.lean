import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811C

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G12
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source23,source5,source24]
def scale : ℕ := 120
def denominator : ℕ := 723067200
def g0 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    93185523056736*a +
    28991551241685*b +
    234099115823850
def identitySlack0 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    4345716045393260208*a +
    1455752762498728905*b +
    10921297343226418650
def helperSlack0 (a b c : ℕ) : ℕ :=
    12362863396782265680*a^3 +
    37147963818243245040*a^2*b +
    37207337446139693040*a^2*c +
    5828330146177580567029*a^2 +
    37207337446139693040*a*b^2 +
    74474048520175834080*a*b*c +
    12984459960075941817698*a*b +
    1244917406882685153958*a*c +
    51596899520159148436690*a +
    211954399591459269437*b^2 +
    420029741542652322274*b*c +
    35190506662249361161322*b +
    3430558334990899229702*c +
    95411111920351630446077
def g1 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    955978300818216*a +
    28991551241685*b +
    28347291401660*c +
    2247288846358650
def identitySlack1 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47335721171275830888*a +
    1455752762498728905*b +
    1423402543151553580*c +
    111176071722933769650
def helperSlack1 (a b c : ℕ) : ℕ :=
    12336145264228864080*a^3 +
    37094527553136441840*a^2*b +
    37180619313586291440*a^2*c +
    5827988190106596752629*a^2 +
    37180619313586291440*a*b^2 +
    74447330387622432480*a*b*c +
    12984033396585205564898*a*b +
    1244648741182479605158*a*c +
    51595457924661507835090*a +
    211869792171706831037*b^2 +
    419945134122899883874*b*c +
    35189686838538060255722*b +
    3429996511918019664902*c +
    95409119041756883310077
def g2 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    955978300818216*a +
    2061584301600*b^2 +
    4123168603200*b*c +
    1177320211457205*b +
    92773196759120*c +
    3774981025983930
def identitySlack2 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47335721171275830888*a +
    103518332536240800*b^2 +
    207036665072481600*b*c +
    58449962530191385545*b +
    4325011905011068000*c +
    186885850723207555890
def helperSlack2 (a b c : ℕ) : ℕ :=
    12303489768885817680*a^3 +
    37029216562450349040*a^2*b +
    37147963818243245040*a^2*c +
    5827502513881349475829*a^2 +
    37147963818243245040*a*b^2 +
    74414674892279386080*a*b*c +
    12983445300851836915298*a*b +
    1244351378221240968358*a*c +
    51593175126136869220690*a +
    211767372663585458237*b^2 +
    419842714614778511074*b*c +
    35188505807295151762922*b +
    3429397332913051719302*c +
    95405768760006344881277
def conductor (a b c : ℕ) : ℕ :=
    37120329817680*a^3 +
    111360989453040*a^2*b +
    111360989453040*a^2*c +
    8209709935433269*a^2 +
    111360989453040*a*b^2 +
    222721978906080*a*b*c +
    16419419870866538*a*b +
    1967652726210598*a*c +
    79313074618006690*a +
    437059959935237*b^2 +
    874119919870474*b*c +
    48667918673826722*b +
    5312617239858902*c +
    165465991306502477
def slope (a b : ℕ) : ℕ :=
    37266711074036141040*a^2 +
    74533422148072282080*a*b +
    1245540830051095905958*a +
    420222705833315778274*b +
    3431890531040506205702
def intercept (a b : ℕ) : ℕ :=
    12422237024678713680*a^3 +
    37266711074036141040*a^2*b +
    5832266977454655651829*a^2 +
    37266711074036141040*a*b^2 +
    12988589755643680358498*a*b +
    51624736962431279515090*a +
    212147363882122725437*b^2 +
    35201101211111387036522*b +
    95459284254921548199677
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 12 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source23,source24,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G12

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G13
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source25,source5,source24]
def scale : ℕ := 120
def denominator : ℕ := 723067200
def g0 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    93185523056736*a +
    28991551241685*b +
    234099115823850
def identitySlack0 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    4345716045393260208*a +
    1455752762498728905*b +
    10921297343226418650
def helperSlack0 (a b c : ℕ) : ℕ :=
    12359894715387443280*a^3 +
    37142026455453600240*a^2*b +
    37204368764744870640*a^2*c +
    5828294906419471259429*a^2 +
    37204368764744870640*a*b^2 +
    74471079838781011680*a*b*c +
    12984417305196165068098*a*b +
    1232473636568687317158*a*c +
    51596765671490845376690*a +
    211946979204336136237*b^2 +
    423127943529221943074*b*c +
    35190437640194862342922*b +
    3399467710854738512902*c +
    95410952447783248748077
def g1 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    955978300818216*a +
    28991551241685*b +
    28862699273680*c +
    2247288846358650
def identitySlack1 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47335721171275830888*a +
    1455752762498728905*b +
    1449282718629293840*c +
    111176071722933769650
def helperSlack1 (a b c : ℕ) : ℕ :=
    12336145264228864080*a^3 +
    37094527553136441840*a^2*b +
    37180619313586291440*a^2*c +
    5827990175809346248229*a^2 +
    37180619313586291440*a*b^2 +
    74447330387622432480*a*b*c +
    12984036378430239615298*a*b +
    1232223277740858075558*a*c +
    51595475379779808450290*a +
    211870783048535694637*b^2 +
    423051747373421501474*b*c +
    35189699558662073387722*b +
    3398934337656550703302*c +
    95409157121457546202477
def g2 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    955978300818216*a +
    2061584301600*b^2 +
    4123168603200*b*c +
    1177320211457205*b +
    90711565271040*c +
    3774981025983930
def identitySlack2 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47335721171275830888*a +
    103518332536240800*b^2 +
    207036665072481600*b*c +
    58449962530191385545*b +
    4221491203100106960*c +
    186885850723207555890
def helperSlack2 (a b c : ℕ) : ℕ :=
    12303489768885817680*a^3 +
    37029216562450349040*a^2*b +
    37147963818243245040*a^2*c +
    5827504499584098971429*a^2 +
    37147963818243245040*a*b^2 +
    74414674892279386080*a*b*c +
    12983448282696870965698*a*b +
    1231925914779619438758*a*c +
    51593192581255169835890*a +
    211768363540414321837*b^2 +
    422949327865300128674*b*c +
    35188518527419164894922*b +
    3398335158651582757702*c +
    95405806839707007773677
def conductor (a b c : ℕ) : ℕ :=
    37120329817680*a^3 +
    111360989453040*a^2*b +
    111360989453040*a^2*c +
    8216291755047269*a^2 +
    111360989453040*a*b^2 +
    222721978906080*a*b*c +
    16432583510094538*a*b +
    1957121814828198*a*c +
    79378892814146690*a +
    438376323858037*b^2 +
    876752647716074*b*c +
    48712675047201922*b +
    5286289961402902*c +
    165609474974087677
def slope (a b : ℕ) : ℕ :=
    37266711074036141040*a^2 +
    74533422148072282080*a*b +
    1233115366609474376358*a +
    423329319083837395874*b +
    3400828356779037244102
def intercept (a b : ℕ) : ℕ :=
    12422237024678713680*a^3 +
    37266711074036141040*a^2*b +
    5832268963157405147429*a^2 +
    37266711074036141040*a*b^2 +
    12988592737488714408898*a*b +
    51624754417549580130290*a +
    212148354758951589037*b^2 +
    35201113931235400168522*b +
    95459322334622211092077
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 13 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source24,source25,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G13

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G14
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source25,source5,source26]
def scale : ℕ := 120
def denominator : ℕ := 723067200
def g0 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    92876278333524*a +
    28991551241685*b +
    233377542443730
def identitySlack0 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    4330187940106616052*a +
    1455752762498728905*b +
    10885064979090453090
def helperSlack0 (a b c : ℕ) : ℕ :=
    12359894715387443280*a^3 +
    37142026455453600240*a^2*b +
    37204368764744870640*a^2*c +
    5895409983373658440037*a^2 +
    37204368764744870640*a*b^2 +
    74471079838781011680*a*b*c +
    13051531409649963747394*a*b +
    1230608283865578112422*a*c +
    52088955135148372715570*a +
    211945989169980183229*b^2 +
    423126953020974977858*b*c +
    35347046844845517532618*b +
    3395112153324021781222*c +
    96194022888884088254893
def g1 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    967111110853848*a +
    28991551241685*b +
    28862699273680*c +
    2273265488042970
def identitySlack1 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47894732961595020504*a +
    1455752762498728905*b +
    1449282718629293840*c +
    112480436831828529810
def helperSlack1 (a b c : ℕ) : ℕ :=
    12336145264228864080*a^3 +
    37094527553136441840*a^2*b +
    37180619313586291440*a^2*c +
    5895105252763533428837*a^2 +
    37180619313586291440*a*b^2 +
    74447330387622432480*a*b*c +
    13051150482884038294594*a*b +
    1230357925037748870822*a*c +
    52087664843437335789170*a +
    211869793014179741629*b^2 +
    423050756865174536258*b*c +
    35346308763312728577418*b +
    3394578780125833971622*c +
    96192227562558385709293
def g2 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    967111110853848*a +
    2061584301600*b^2 +
    4123168603200*b*c +
    1177320211457205*b +
    90711565271040*c +
    3800957667668250
def identitySlack2 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47894732961595020504*a +
    103518332536240800*b^2 +
    207036665072481600*b*c +
    58449962530191385545*b +
    4221491203100106960*c +
    188190215832102316050
def helperSlack2 (a b c : ℕ) : ℕ :=
    12306458450280640080*a^3 +
    37035153925239993840*a^2*b +
    37150932499638067440*a^2*c +
    5894621177822407086437*a^2 +
    37150932499638067440*a*b^2 +
    74417643573674208480*a*b*c +
    13050572399698742576194*a*b +
    1230083816751211245222*a*c +
    52085257553601318419570*a +
    211775784770010365629*b^2 +
    422956748621005160258*b*c +
    35345111507762302895818*b +
    3394021657451950717222*c +
    96188585877461954333293
def conductor (a b c : ℕ) : ℕ :=
    37120329817680*a^3 +
    111360989453040*a^2*b +
    111360989453040*a^2*c +
    8233351831486757*a^2 +
    111360989453040*a*b^2 +
    222721978906080*a*b*c +
    16466703662973514*a*b +
    1956174032803782*a*c +
    79549493578541570*a +
    437902432845829*b^2 +
    875804865691658*b*c +
    48813139941790018*b +
    5281551051280822*c +
    165965841015268093
def slope (a b : ℕ) : ℕ :=
    37266711074036141040*a^2 +
    74533422148072282080*a*b +
    1231250013906365171622*a +
    423328328575590430658*b +
    3396472799248320512422
def intercept (a b : ℕ) : ℕ :=
    12422237024678713680*a^3 +
    37266711074036141040*a^2*b +
    5899384040111592328037*a^2 +
    37266711074036141040*a*b^2 +
    13055706841942513088194*a*b +
    52116943881207107469170*a +
    212147364724595636029*b^2 +
    35357723135886055358218*b +
    96242392775723050598893
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 14 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source25,source26,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G14

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G15
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source21,source5,source26]
def scale : ℕ := 120
def denominator : ℕ := 723067200
def g0 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    92876278333524*a +
    28991551241685*b +
    233377542443730
def identitySlack0 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    4330187940106616052*a +
    1455752762498728905*b +
    10885064979090453090
def helperSlack0 (a b c : ℕ) : ℕ :=
    12356926033992620880*a^3 +
    37136089092663955440*a^2*b +
    37201400083350048240*a^2*c +
    5895374760728280128837*a^2 +
    37201400083350048240*a*b^2 +
    74468111157386189280*a*b*c +
    13051488788995648990594*a*b +
    1230587008311806982822*a*c +
    52088821457607379619570*a +
    211938567466493127229*b^2 +
    423119531317487921858*b*c +
    35346977920201949001418*b +
    3395077766088427832422*c +
    96193863770417601790093
def g1 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    967111110853848*a +
    28991551241685*b +
    28862699273680*c +
    2273265488042970
def identitySlack1 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47894732961595020504*a +
    1455752762498728905*b +
    1449282718629293840*c +
    112480436831828529810
def helperSlack1 (a b c : ℕ) : ℕ :=
    12336145264228864080*a^3 +
    37094527553136441840*a^2*b +
    37180619313586291440*a^2*c +
    5895123088546452973637*a^2 +
    37180619313586291440*a*b^2 +
    74447330387622432480*a*b*c +
    13051168342361508449794*a*b +
    1230357925037748870822*a*c +
    52087803124101675256370*a +
    211869793014179741629*b^2 +
    423050756865174536258*b*c +
    35346357888723046809418*b +
    3394578780125833971622*c +
    96192472976460943740493
def g2 (a b c : ℕ) : ℕ :=
    2061584301600*a^2 +
    4123168603200*a*b +
    4123168603200*a*c +
    967111110853848*a +
    2061584301600*b^2 +
    4123168603200*b*c +
    1177320211457205*b +
    90711565271040*c +
    3800957667668250
def identitySlack2 (a b c : ℕ) : ℕ :=
    103518332536240800*a^2 +
    207036665072481600*a*b +
    207036665072481600*a*c +
    47894732961595020504*a +
    103518332536240800*b^2 +
    207036665072481600*b*c +
    58449962530191385545*b +
    4221491203100106960*c +
    188190215832102316050
def helperSlack2 (a b c : ℕ) : ℕ :=
    12306458450280640080*a^3 +
    37035153925239993840*a^2*b +
    37150932499638067440*a^2*c +
    5894639013605326631237*a^2 +
    37150932499638067440*a*b^2 +
    74417643573674208480*a*b*c +
    13050590259176212731394*a*b +
    1230083816751211245222*a*c +
    52085395834265657886770*a +
    211775784770010365629*b^2 +
    422956748621005160258*b*c +
    35345160633172621127818*b +
    3394021657451950717222*c +
    96188831291364512364493
def conductor (a b c : ℕ) : ℕ :=
    37120329817680*a^3 +
    111360989453040*a^2*b +
    111360989453040*a^2*c +
    8257046382097157*a^2 +
    111360989453040*a*b^2 +
    222721978906080*a*b*c +
    16514092764194314*a*b +
    1956174032803782*a*c +
    79786439084645570*a +
    437902432845829*b^2 +
    875804865691658*b*c +
    48955307245452418*b +
    5281551051280822*c +
    166463426578086493
def slope (a b : ℕ) : ℕ :=
    37266711074036141040*a^2 +
    74533422148072282080*a*b +
    1231250013906365171622*a +
    423328328575590430658*b +
    3396472799248320512422
def intercept (a b : ℕ) : ℕ :=
    12422237024678713680*a^3 +
    37266711074036141040*a^2*b +
    5899401875894511872837*a^2 +
    37266711074036141040*a*b^2 +
    13055724701419983243394*a*b +
    52117082161871446936370*a +
    212147364724595636029*b^2 +
    35357772261296373590218*b +
    96242638189625608630093
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 15 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source21,source26,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G15


