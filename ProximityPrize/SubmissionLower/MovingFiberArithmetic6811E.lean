import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811D

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G16
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source27,source27,source27]
def scale : ℕ := 9
def denominator : ℕ := 4065714
def gLo0 (b c : ℕ) : ℕ :=
    3135405621545*b +
    25727621663120
def identitySlackLo0 (b c : ℕ) : ℕ :=
    157378549767829730*b +
    1228843435773616880
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1555873615621602828*b^2 +
    3111986581180663212*b*c +
    226338789646999664946*b +
    27810306194082258132*c +
    640832924330161304688
def gLo1 (b c : ℕ) : ℕ :=
    3135405621545*b +
    3135405621545*c +
    214926242891650
def identitySlackLo1 (b c : ℕ) : ℕ :=
    157378549767829730*b +
    157378549767829730*c +
    10662950223733423300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1555873615621602828*b^2 +
    3111986581180663212*b*c +
    226338789646999664946*b +
    27810306194082258132*c +
    640832924330161304688
def gLo2 (b c : ℕ) : ℕ :=
    103080787968*b^2 +
    206161575936*b*c +
    93254720955032*b +
    9852907357087*c +
    329451867638368
def identitySlackLo2 (b c : ℕ) : ℕ :=
    5174037071265792*b^2 +
    10348074142531584*b*c +
    4630804418828853488*b +
    469545309487613518*c +
    16336414674266836192
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1555873615621602828*b^2 +
    3111986581180663212*b*c +
    226338789646999664946*b +
    27810306194082258132*c +
    640832924330161304688
def conductorLo (b c : ℕ) : ℕ :=
    7016724416430*b^2 +
    14033448832860*b*c +
    559393585224372*b +
    89886079035720*c +
    1880516027263716
def slopeLo (b : ℕ) : ℕ :=
    3112743594936342924*b +
    27815377074062097357
def interceptLo (b : ℕ) : ℕ :=
    1556630629377282540*b^2 +
    226362450318381572409*b +
    640932385242997251054
def gHi0 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    10213690114975*a +
    3290026803497*b +
    35786689809711
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    5174037071265792*a^2 +
    10348074142531584*a*b +
    487654439237043790*a +
    165139605374728418*b +
    1708736779929594174
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    46333082890946700*a^3 +
    139233032332682364*a^2*b +
    139466815992524628*a^2*c +
    42508931462675866692*a^2 +
    139466815992524628*a*b^2 +
    279167415644891520*a*b*c +
    85008531919486373496*a*b +
    9716261889986698968*a*c +
    444431475323894739636*a +
    1672057264793431392*b^2 +
    3344587663184162604*b*c +
    311138238678423757614*b +
    37317251412346834008*c +
    1042755234230094711660
def gHi1 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    93460882530968*a +
    3290026803497*b +
    3290026803497*c +
    308232503454234
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    5174037071265792*a^2 +
    10348074142531584*a*b +
    10348074142531584*a*c +
    4641152492971385072*a +
    165139605374728418*b +
    165139605374728418*c +
    15296341621623741876
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    46333082890946700*a^3 +
    139233032332682364*a^2*b +
    139466815992524628*a^2*c +
    42508931462675866692*a^2 +
    139466815992524628*a*b^2 +
    279167415644891520*a*b*c +
    85008531919486373496*a*b +
    9716261889986698968*a*c +
    444431475323894739636*a +
    1672057264793431392*b^2 +
    3344587663184162604*b*c +
    311138238678423757614*b +
    37317251412346834008*c +
    1042755234230094711660
def gHi2 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    93460882530968*a +
    103080787968*b^2 +
    206161575936*b*c +
    93460882530968*b +
    10059068933023*c +
    422809669381368
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    5174037071265792*a^2 +
    10348074142531584*a*b +
    10348074142531584*a*c +
    4641152492971385072*a +
    5174037071265792*b^2 +
    10348074142531584*b*c +
    4641152492971385072*b +
    479893383630145102*c +
    20972393130166955472
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    46333082890946700*a^3 +
    139233032332682364*a^2*b +
    139466815992524628*a^2*c +
    42508931462675866692*a^2 +
    139466815992524628*a*b^2 +
    279167415644891520*a*b*c +
    85008531919486373496*a*b +
    9716261889986698968*a*c +
    444431475323894739636*a +
    1672057264793431392*b^2 +
    3344587663184162604*b*c +
    311138238678423757614*b +
    37317251412346834008*c +
    1042755234230094711660
def conductorHi (a b c : ℕ) : ℕ :=
    532909396836*a^3 +
    1598728190508*a^2*b +
    1598728190508*a^2*c +
    95748724783728*a^2 +
    1598728190508*a*b^2 +
    3197456381016*a*b*c +
    191497449567456*a*b +
    34994947504572*a*c +
    1091430482546448*a +
    8615452606938*b^2 +
    17230905213876*b*c +
    749292306601320*b +
    123282298349784*c +
    2876730694423272
def slopeHi (a b : ℕ) : ℕ :=
    139700599652366892*a^2 +
    279401199304733784*a*b +
    9719122956978232620*a +
    3345578460599684580*b +
    37324949575658364621
def interceptHi (a b : ℕ) : ℕ :=
    46566866550788964*a^3 +
    139700599652366892*a^2*b +
    42518575897201037232*a^2 +
    139700599652366892*a*b^2 +
    85019167151427066012*a*b +
    444508836904074025584*a +
    1673048062208953368*b^2 +
    311172067014426673065*b +
    1042922646072244615698
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80880*identityDegree f a b c ≤ 50194*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50194*graphDir cfg scale f 0 b c = scale*131073*80880*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50194*graphDir cfg scale f (a+1) b c = scale*131073*80880*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50194*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50194
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50194) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50194)*50194 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G16

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G17
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source28,source28,source28]
def scale : ℕ := 15
def denominator : ℕ := 11293650
def gLo0 (b c : ℕ) : ℕ :=
    4595731333555*b +
    37496182803960
def identitySlackLo0 (b c : ℕ) : ℕ :=
    230678138556459670*b +
    1777868723020254240
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3847192284040034370*b^2 +
    7695428245132935990*b*c +
    651735605778707228274*b +
    67698043891131544914*c +
    1849766283287652191844
def gLo1 (b c : ℕ) : ℕ :=
    4595731333555*b +
    4595731333555*c +
    371439265676110
def identitySlackLo1 (b c : ℕ) : ℕ :=
    230678138556459670*b +
    230678138556459670*c +
    18435593148063237340
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3847192284040034370*b^2 +
    7695428245132935990*b*c +
    651735605778707228274*b +
    67698043891131544914*c +
    1849766283287652191844
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    161597993008116*b +
    14405689214281*c +
    570974310166480
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8623395118776320*b^2 +
    17246790237552640*b*c +
    8027877919736003304*b +
    681393293764934914*c +
    28325997241207285120
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3847192284040034370*b^2 +
    7695428245132935990*b*c +
    651735605778707228274*b +
    67698043891131544914*c +
    1849766283287652191844
def conductorLo (b c : ℕ) : ℕ :=
    11102401072170*b^2 +
    22204802144340*b*c +
    964771893319644*b +
    136072492498584*c +
    3253687154468244
def slopeLo (b : ℕ) : ℕ :=
    7698559276291537740*b +
    67718843992671846339
def interceptLo (b : ℕ) : ℕ :=
    3850323315198636120*b^2 +
    651843461870384054499*b +
    1850227619701299107394
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    15006993810761*a +
    4853433303475*b +
    52245473334081
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    711575176680652034*a +
    243613231234624150*b +
    2476508741232462114
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    122747490591012487014*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    245449190529546986928*a*b +
    23952924192266820708*a*c +
    1283758451063112500838*a +
    4169598166958454450*b^2 +
    8341214109552452250*b*c +
    896604661683500986422*b +
    91069859360062460742*c +
    3010776268575643467228
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    161941595634676*a +
    4853433303475*b +
    4853433303475*c +
    533123158030146
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    17246790237552640*a*c +
    8045124709973555944*a +
    243613231234624150*b +
    243613231234624150*c +
    26467782699568349124
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    122747490591012487014*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    245449190529546986928*a*b +
    23952924192266820708*a*c +
    1283758451063112500838*a +
    4169598166958454450*b^2 +
    8341214109552452250*b*c +
    896604661683500986422*b +
    91069859360062460742*c +
    3010776268575643467228
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    161941595634676*a +
    171801313280*b^2 +
    343602626560*b*c +
    161941595634676*b +
    14749291840841*c +
    732744104487876
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    17246790237552640*a*c +
    8045124709973555944*a +
    8623395118776320*b^2 +
    17246790237552640*b*c +
    8045124709973555944*b +
    698640084002487554*c +
    36362498556062064744
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    122747490591012487014*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    245449190529546986928*a*b +
    23952924192266820708*a*c +
    1283758451063112500838*a +
    4169598166958454450*b^2 +
    8341214109552452250*b*c +
    896604661683500986422*b +
    91069859360062460742*c +
    3010776268575643467228
def conductorHi (a b c : ℕ) : ℕ :=
    888182328060*a^3 +
    2664546984180*a^2*b +
    2664546984180*a^2*c +
    165384176267304*a^2 +
    2664546984180*a*b^2 +
    5329093968360*a*b*c +
    330768352534608*a*b +
    54535218927588*a*c +
    1888686423777168*a +
    13766948056350*b^2 +
    27533896112700*b*c +
    1292875698870072*b +
    187943164441992*c +
    4977877584306168
def slopeHi (a b : ℕ) : ℕ :=
    388055444891918580*a^2 +
    776110889783837160*a*b +
    23964744802496823708*a +
    8345319239293730100*b +
    91101505973250089067
def interceptHi (a b : ℕ) : ℕ :=
    129351814963972860*a^3 +
    388055444891918580*a^2*b +
    122791108272730127664*a^2 +
    388055444891918580*a*b^2 +
    245496913341005905428*a*b +
    1284114200110040673288*a +
    4173703296699732300*b^2 +
    896758292389471378947*b +
    3011550710453083590678
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80880*identityDegree f a b c ≤ 50194*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50194*graphDir cfg scale f 0 b c = scale*131073*80880*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50194*graphDir cfg scale f (a+1) b c = scale*131073*80880*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50194*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50194
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50194) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50194)*50194 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G17

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G18
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source29,source29,source29]
def scale : ℕ := 15
def denominator : ℕ := 11293650
def gLo0 (b c : ℕ) : ℕ :=
    4406747922849*b +
    36826146147760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    221192305239482706*b +
    1744236903098951440
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3704904606643493346*b^2 +
    7410852890339853942*b*c +
    702673369101428295582*b +
    66482042276767409124*c +
    1997435938795675288902
def gLo1 (b c : ℕ) : ℕ :=
    4406747922849*b +
    4406747922849*c +
    400620089803980
def identitySlackLo1 (b c : ℕ) : ℕ :=
    221192305239482706*b +
    221192305239482706*c +
    19900295434337544120
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3704904606643493346*b^2 +
    7410852890339853942*b*c +
    702673369101428295582*b +
    66482042276767409124*c +
    1997435938795675288902
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    174543356641477*b +
    14216705803575*c +
    616871821116180
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8623395118776320*b^2 +
    17246790237552640*b*c +
    8677657501948925338*b +
    671907460447957950*c +
    30629776905816526920
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3704904606643493346*b^2 +
    7410852890339853942*b*c +
    702673369101428295582*b +
    66482042276767409124*c +
    1997435938795675288902
def conductorLo (b c : ℕ) : ℕ :=
    10924759185606*b^2 +
    21849518371212*b*c +
    1037072141151192*b +
    134296073632944*c +
    3508514440744302
def slopeLo (b : ℕ) : ℕ :=
    7413983921498455692*b +
    66502799858131482624
def interceptLo (b : ℕ) : ℕ :=
    3708035637802095096*b^2 +
    702787050457248347532*b +
    1997926398801868072752
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    14818010400055*a +
    4664449892769*b +
    51386453267175
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    702089343363675070*a +
    234127397917647186*b +
    2433391087994182350
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    132498433048416074958*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    264946838888613635016*a*b +
    23668317913709209260*a*c +
    1386583452785928669516*a +
    4027310489561913426*b^2 +
    8056638754759370202*b*c +
    967040073365288701818*b +
    89569251467140713504*c +
    3251519983349079145020
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    174886959268037*a +
    4664449892769*b +
    4664449892769*c +
    575249345791377
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    17246790237552640*a*c +
    8694904292186477978*a +
    234127397917647186*b +
    234127397917647186*c +
    28582264568055577938
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    132498433048416074958*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    264946838888613635016*a*b +
    23668317913709209260*a*c +
    1386583452785928669516*a +
    4027310489561913426*b^2 +
    8056638754759370202*b*c +
    967040073365288701818*b +
    89569251467140713504*c +
    3251519983349079145020
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    174886959268037*a +
    171801313280*b^2 +
    343602626560*b*c +
    174886959268037*b +
    14560308430135*c +
    791586979070937
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8623395118776320*a^2 +
    17246790237552640*a*b +
    17246790237552640*a*c +
    8694904292186477978*a +
    8623395118776320*b^2 +
    17246790237552640*b*c +
    8694904292186477978*b +
    689154250685510590*c +
    39316057802884228578
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128377716381296760*a^3 +
    386107247726566380*a^2*b +
    387081346309242480*a^2*c +
    132498433048416074958*a^2 +
    387081346309242480*a*b^2 +
    775136791201161060*a*b*c +
    264946838888613635016*a*b +
    23668317913709209260*a*c +
    1386583452785928669516*a +
    4027310489561913426*b^2 +
    8056638754759370202*b*c +
    967040073365288701818*b +
    89569251467140713504*c +
    3251519983349079145020
def conductorHi (a b c : ℕ) : ℕ :=
    888182328060*a^3 +
    2664546984180*a^2*b +
    2664546984180*a^2*c +
    177552645496938*a^2 +
    2664546984180*a*b^2 +
    5329093968360*a*b*c +
    355105290993876*a*b +
    54179935154460*a*c +
    2034708054532776*a +
    13589306169786*b^2 +
    27178612339572*b*c +
    1389512885160888*b +
    185811461803224*c +
    5366558032108200
def slopeHi (a b : ℕ) : ℕ :=
    388055444891918580*a^2 +
    776110889783837160*a*b +
    23680123062056947560*a +
    8060743884500648052*b +
    89600840098269849204
def interceptHi (a b : ℕ) : ℕ :=
    129351814963972860*a^3 +
    388055444891918580*a^2*b +
    132544169008003979508*a^2 +
    388055444891918580*a*b^2 +
    264996679977942817416*a*b +
    1386959854132701828216*a +
    4031415619303191276*b^2 +
    967201647613272583968*b +
    3252342082841039859120
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80880*identityDegree f a b c ≤ 50194*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50194*graphDir cfg scale f 0 b c = scale*131073*80880*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50194*graphDir cfg scale f (a+1) b c = scale*131073*80880*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50194*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50194
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50194) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50194)*50194 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G18

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G19
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source30,source30,source30]
def scale : ℕ := 21
def denominator : ℕ := 22135554
def gLo0 (b c : ℕ) : ℕ :=
    6056057045565*b +
    49049989550670
def identitySlackLo0 (b c : ℕ) : ℕ :=
    303977727345089610*b +
    2316114628207930380
def helperSlackLo0 (b c : ℕ) : ℕ :=
    7141570114860001530*b^2 +
    14285701026660682674*b*c +
    1301009473732449034908*b +
    124141937333044458690*c +
    3696532358185053527292
def gLo1 (b c : ℕ) : ℕ :=
    6056057045565*b +
    6056057045565*c +
    529670323613610
def identitySlackLo1 (b c : ℕ) : ℕ :=
    303977727345089610*b +
    303977727345089610*c +
    26294471128864741140
def helperSlackLo1 (b c : ℕ) : ℕ :=
    7141570114860001530*b^2 +
    14285701026660682674*b*c +
    1301009473732449034908*b +
    124141937333044458690*c +
    3696532358185053527292
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    230697198704024*b +
    18863979366122*c +
    815176899319392
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12072753166286848*b^2 +
    24145506332573696*b*c +
    11462894753911060976*b +
    888498361383767828*c +
    40450107087832945248
def helperSlackLo2 (b c : ℕ) : ℕ :=
    7141570114860001530*b^2 +
    14285701026660682674*b*c +
    1301009473732449034908*b +
    124141937333044458690*c +
    3696532358185053527292
def conductorLo (b c : ℕ) : ℕ :=
    15188077727910*b^2 +
    30376155455820*b*c +
    1374413606692452*b +
    181725980301756*c +
    4641780200144148
def slopeLo (b : ℕ) : ℕ :=
    14293625859796632012*b +
    124194729158112288636
def interceptLo (b : ℕ) : ℕ :=
    7149494947995950868*b^2 +
    1301301918607984822134*b +
    3697797310790611759218
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19705805801194*a +
    6416839803453*b +
    68395010758968
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    930752997465771796*a +
    322086857094519882*b +
    3228758403817880352
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251074331518939320*a^3 +
    755677722985161732*a^2*b +
    758132451413505504*a^2*c +
    245325517212938721042*a^2 +
    758132451413505504*a*b^2 +
    1518719631255354780*a*b*c +
    490520878976446579032*a*b +
    44197158359957592660*a*c +
    2566167373080048552750*a +
    7772938658027495130*b^2 +
    15550892841424013646*b*c +
    1790394381326938193904*b +
    167200669582616287542*c +
    6017371756698721829328
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    231178242381208*a +
    6416839803453*b +
    6416839803453*c +
    760487781401922
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    11487040260243634672*a +
    322086857094519882*b +
    322086857094519882*c +
    37763402167252553988
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251074331518939320*a^3 +
    755677722985161732*a^2*b +
    758132451413505504*a^2*c +
    245325517212938721042*a^2 +
    758132451413505504*a*b^2 +
    1518719631255354780*a*b*c +
    490520878976446579032*a*b +
    44197158359957592660*a*c +
    2566167373080048552750*a +
    7772938658027495130*b^2 +
    15550892841424013646*b*c +
    1790394381326938193904*b +
    167200669582616287542*c +
    6017371756698721829328
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    231178242381208*a +
    240521838592*b^2 +
    481043677184*b*c +
    231178242381208*b +
    19345023043306*c +
    1046114619862008
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    11487040260243634672*a +
    12072753166286848*b^2 +
    24145506332573696*b*c +
    11487040260243634672*b +
    912643867716341524*c +
    51925074594910293072
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251074331518939320*a^3 +
    755677722985161732*a^2*b +
    758132451413505504*a^2*c +
    245325517212938721042*a^2 +
    758132451413505504*a*b^2 +
    1518719631255354780*a*b*c +
    490520878976446579032*a*b +
    44197158359957592660*a*c +
    2566167373080048552750*a +
    7772938658027495130*b^2 +
    15550892841424013646*b*c +
    1790394381326938193904*b +
    167200669582616287542*c +
    6017371756698721829328
def conductorHi (a b c : ℕ) : ℕ :=
    1243455259284*a^3 +
    3730365777852*a^2*b +
    3730365777852*a^2*c +
    235730195297136*a^2 +
    3730365777852*a*b^2 +
    7460731555704*a*b*c +
    471460390594272*a*b +
    73897848464040*a*c +
    2694469175562960*a +
    18918443505762*b^2 +
    37836887011524*b*c +
    1842143631508872*b +
    251893462987944*c +
    7101762635669256
def slopeHi (a b : ℕ) : ℕ :=
    760587179841849276*a^2 +
    1521174359683698552*a*b +
    44227054530913053120*a +
    15561272402988306756*b +
    167280902850211234176
def interceptHi (a b : ℕ) : ℕ :=
    253529059947283092*a^3 +
    760587179841849276*a^2*b +
    245442849908076616188*a^2 +
    760587179841849276*a*b^2 +
    490648591233148767288*a*b +
    2567136252352210420194*a +
    7783318219591788240*b^2 +
    1790809629002319481842*b +
    6019490710609732377324
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80880*identityDegree f a b c ≤ 50194*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50194*graphDir cfg scale f 0 b c = scale*131073*80880*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50194*graphDir cfg scale f (a+1) b c = scale*131073*80880*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50194*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50194
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50194) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50194)*50194 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G19

