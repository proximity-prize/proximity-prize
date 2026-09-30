import ProximityPrize.SubmissionLower.MovingFiberArithmetic6815E
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G20
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source31,source32,source33]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    211060019056110*b +
    1854450095271620
def identitySlackLo0 (b c : ℕ) : ℕ :=
    10589725396121263140*b +
    87207714057190641880
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10110092451521858794692*b^2 +
    20261755113028677105384*b*c +
    2394620472839352201274884*b +
    187189713479449766250396*c +
    6380530717927026198914814
def gLo1 (b c : ℕ) : ℕ :=
    211060019056110*b +
    212004936109640*c +
    21565467406099540
def identitySlackLo1 (b c : ℕ) : ℕ :=
    10589725396121263140*b +
    10637135664365077360*c +
    1070350831587703079960
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10107837738002491181892*b^2 +
    20259500399509309492584*b*c +
    2394601295244087193201284*b +
    187174039580710958984796*c +
    6380490914251538740313214
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    11601992045155085*b +
    720542160717800*c +
    36047048873537170
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    577448376855237138790*b +
    33817496362667849200*c +
    1789944724292964007580
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10103231334038191757892*b^2 +
    20254893995545010068584*b*c +
    2394547030109225810161284*b +
    187147273942781282610396*c +
    6380334508076598278489214
def conductorLo (b c : ℕ) : ℕ :=
    20076305040521892*b^2 +
    40152610081043784*b*c +
    2367441551250391284*b +
    242589846110389596*c +
    8062237904287234014
def slopeLo (b : ℕ) : ℕ :=
    20273052924856906218984*b +
    187266604075306403879196
def interceptLo (b : ℕ) : ℕ :=
    10121390263350087908292*b^2 +
    2395223582973417647857284*b +
    6383265138935225735167614
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    758372853156212*a +
    225491329371630*b +
    2598391564711992
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    35715613525072732888*a +
    11313801959892163620*b +
    122199247335704818608
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    401993413389517860960*a^3 +
    1209471409488864725280*a^2*b +
    1212962578809175867680*a^2*c +
    400240286962861745768886*a^2 +
    1212962578809175867680*a*b^2 +
    2429416326938662877760*a*b*c +
    892458730502271549063132*a*b +
    68005121794272047306916*a*c +
    4304640517079016345014952*a +
    11120313592475182527972*b^2 +
    22285688564255635714344*b*c +
    3285261504525025698438336*b +
    253373645287803450515232*c +
    10284927452393775350210640
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    9431199537275964*a +
    225491329371630*b +
    226436246425160*c +
    30982235559659664
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    468531033564910121736*a +
    11313801959892163620*b +
    11361212228135977840*c +
    1538157784906054645536
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401266086447786372960*a^3 +
    1208016755605401749280*a^2*b +
    1212235251867444379680*a^2*c +
    400229809056438011615286*a^2 +
    1212235251867444379680*a*b^2 +
    2428688999996931389760*a*b*c +
    892445270555386715808732*a*b +
    67996175671963898916516*a*c +
    4304590448252494287062952*a +
    11117331552014083427172*b^2 +
    22282706523794536613544*b*c +
    3285230321636759320086336*b +
    253349752593698226347232*c +
    10284847330471247836322640
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    9431199537275964*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    11621233792242445*b +
    739783907805160*c +
    45468627537269454
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    468531033564910121736*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    578413812273598339430*b +
    34782931781029049840*c +
    2257993040148693528996
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    399811432564323396960*a^3 +
    1205107447838475797280*a^2*b +
    1210780597983981403680*a^2*c +
    400203325558833383999286*a^2 +
    1210780597983981403680*a*b^2 +
    2427234346113468413760*a*b*c +
    892412725999934325792732*a*b +
    67980029012007757706916*a*c +
    4304436300571297238390952*a +
    11111270494166321027172*b^2 +
    22276645465946774213544*b*c +
    3285146421254212472982336*b +
    253308294949695871739232*c +
    10284561805458831490466640
def conductorHi (a b c : ℕ) : ℕ :=
    1706998124734560*a^3 +
    5120994374203680*a^2*b +
    5120994374203680*a^2*c +
    404233863198633846*a^2 +
    5120994374203680*a*b^2 +
    10241988748407360*a*b*c +
    808467726397267692*a*b +
    100183824683933796*a*c +
    4666450560912273672*a +
    25197299414725572*b^2 +
    50394598829451144*b*c +
    3170788283273455296*b +
    337652676420119712*c +
    12326161600125608400
def slopeHi (a b : ℕ) : ℕ :=
    1216453748129487010080*a^2 +
    2432907496258974020160*a*b +
    68048276530587400817316*a +
    22300477545404175970344*b +
    253490199450655130512032
def interceptHi (a b : ℕ) : ℕ :=
    405484582709829003360*a^3 +
    1216453748129487010080*a^2*b +
    400475157096122008520886*a^2 +
    1216453748129487010080*a*b^2 +
    892708389616680352071132*a*b +
    4306681547350515116563752*a +
    11135102573623722783972*b^2 +
    3286107291434859325743936*b +
    10289471524709533706402640
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
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80900*identityDegree f a b c ≤ 50174*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50174*graphDir cfg scale f 0 b c = scale*131073*80900*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50174*graphDir cfg scale f (a+1) b c = scale*131073*80900*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50174*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50174
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50174) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50174)*50174 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G20
