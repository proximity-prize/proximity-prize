import ProximityPrize.SubmissionLower.MergedInfra6815_22
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G0
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source0,source0,source0]
def scale : ℕ := 18
def denominator : ℕ := 16256376
def gLo0 (b c : ℕ) : ℕ :=
    5325894189560*b +
    46601779286330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    267168156125087840*b +
    2212627657794813020
def helperSlackLo0 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204695979330368*b +
    100761785620725304728*c +
    2488187413167318047160
def gLo1 (b c : ℕ) : ℕ :=
    5325894189560*b +
    5325894189560*c +
    416623600372320
def identitySlackLo1 (b c : ℕ) : ℕ :=
    267168156125087840*b +
    267168156125087840*c +
    20649298292427770280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204695979330368*b +
    100761785620725304728*c +
    2488187413167318047160
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    181217906410296*b +
    18099455723173*c +
    640142708903136
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10341889295253504*b^2 +
    20683778590507008*b*c +
    8990531858506372464*b +
    857899497567392332*c +
    31711785672993858504
def helperSlackLo2 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204695979330368*b +
    100761785620725304728*c +
    2488187413167318047160
def fullSlackLo (b c : ℕ) : ℕ :=
    1069988205126240*b^2 +
    2139976410252480*b*c +
    174767255569530720*b +
    20079348270294420*c +
    495661800932403840
def fullSlackHi (a b c : ℕ) : ℕ :=
    37109083668480*a^3 +
    111327251005440*a^2*b +
    111327251005440*a^2*c +
    32916095823201120*a^2 +
    111327251005440*a*b^2 +
    222654502010880*a*b*c +
    65832191646402240*a*b +
    7165213024540680*a*c +
    344042737675644960*a +
    1162760914297440*b^2 +
    2325521828594880*b*c +
    240432456056309280*b +
    27077570135211420*c +
    806788442218616640
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    13140001626840*b^2 +
    26280003253680*b*c +
    1084958017591752*b +
    167092978720716*c +
    3651570224764920
def slopeLo (b : ℕ) : ℕ :=
    10740750868698756048*b +
    100797387539742083808
def interceptLo (b : ℕ) : ℕ :=
    5372178908296732632*b^2 +
    877297135010830192044*b +
    2488942429543936937880
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    18821021238949*a +
    5635136553464*b +
    65113556588511
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    894096110100779596*a +
    282680990067968096*b +
    3091210855051562664
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724450567407568*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923907146017408*a*b +
    35946531869381896356*a*c +
    1727020461327157047312*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470138553562200*b +
    135872055937582211412*c +
    4049981545180340976624
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    181630229562168*a +
    5635136553464*b +
    5635136553464*c +
    597944585997720
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    20683778590507008*a*c +
    9011215637096879472*a +
    282680990067968096*b +
    282680990067968096*c +
    29645001016680619800
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724450567407568*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923907146017408*a*b +
    35946531869381896356*a*c +
    1727020461327157047312*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470138553562200*b +
    135872055937582211412*c +
    4049981545180340976624
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    181630229562168*a +
    206161575936*b^2 +
    412323151872*b*c +
    181630229562168*b +
    18511778875045*c +
    821566776889368
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    20683778590507008*a*c +
    9011215637096879472*a +
    10341889295253504*b^2 +
    20683778590507008*b*c +
    9011215637096879472*b +
    878583276157899340*c +
    40712659420795484472
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724450567407568*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923907146017408*a*b +
    35946531869381896356*a*c +
    1727020461327157047312*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470138553562200*b +
    135872055937582211412*c +
    4049981545180340976624
def conductorHi (a b c : ℕ) : ℕ :=
    1065394113912*a^3 +
    3196182341736*a^2*b +
    3196182341736*a^2*c +
    186449155718544*a^2 +
    3196182341736*a*b^2 +
    6392364683472*a*b*c +
    372898311437088*a*b +
    66943298480076*a*c +
    2122327304320032*a +
    16336183968576*b^2 +
    32672367937152*b*c +
    1454660146687104*b +
    230840094859056*c +
    5588513767480320
def slopeHi (a b : ℕ) : ℕ :=
    558576545377036392*a^2 +
    1117153090754072784*a*b +
    35966436880172627844*a +
    11671712843054597280*b +
    135925959779436517884
def interceptHi (a b : ℕ) : ℕ :=
    186192181792345464*a^3 +
    558576545377036392*a^2*b +
    165296147255651566080*a^2 +
    558576545377036392*a*b^2 +
    330453159836031293328*a*b +
    1727602573549223814264*a +
    5837659895474653248*b^2 +
    1206912430206383291604*b +
    4051248854061895679880
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G0

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G1
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source1,source1,source1]
def scale : ℕ := 21
def denominator : ℕ := 22126734
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    47160143516040
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280095636097083200*b +
    2219786774626544610
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791187550936804*b +
    119313871648306985418*c +
    4763039898486765736194
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    680900360593670
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280095636097083200*b +
    280095636097083200*c +
    33864776359396689980
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791187550936804*b +
    119313871648306985418*c +
    4763039898486765736194
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    297502834388595*b +
    18297029134004*c +
    1052034857286092
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12065537511129088*b^2 +
    24131075022258176*b*c +
    14807168452499810820*b +
    859470303593342276*c +
    52307221208405953988
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791187550936804*b +
    119313871648306985418*c +
    4763039898486765736194
def fullSlackLo (b c : ℕ) : ℕ :=
    1324084447260960*b^2 +
    2648168894521920*b*c +
    332760995539069230*b +
    23775869870686920*c +
    948760444982148960
def fullSlackHi (a b c : ℕ) : ℕ :=
    50509586104320*a^3 +
    151528758312960*a^2*b +
    151528758312960*a^2*c +
    62879671910439510*a^2 +
    151528758312960*a*b^2 +
    303057516625920*a*b*c +
    125759343820879020*a*b +
    8568669993107280*a*c +
    658913207167068210*a +
    1450358412521760*b^2 +
    2900716825043520*b*c +
    458293045837127130*b +
    32117246340973080*c +
    1544793979468074300
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    14738098216500*b^2 +
    29476196433000*b*c +
    1748718567576576*b +
    176681579933844*c +
    5956354047058902
def slopeLo (b : ℕ) : ℕ :=
    13292043376162834824*b +
    119363685977955660576
def interceptLo (b : ℕ) : ℕ :=
    6648567332377477620*b^2 +
    1670475678820363062243*b +
    4764585686079587933058
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19138855569076*a +
    5944381276688*b +
    65938214492220
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    901699684882294084*a +
    298193942363776832*b +
    3103388061190803750
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035932906197042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239237968032520*a*b +
    42985986833672287212*a*c +
    3307868994650517369360*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149968622704944*b +
    161161705128390097350*c +
    7755243581683716758712
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    297983878065779*a +
    5944381276688*b +
    5944381276688*c +
    978523454066553
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    14831299527522068996*a +
    298193942363776832*b +
    298193942363776832*c +
    48677977488600724032
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035932906197042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239237968032520*a*b +
    42985986833672287212*a*c +
    3307868994650517369360*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149968622704944*b +
    161161705128390097350*c +
    7755243581683716758712
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    297983878065779*a +
    240521838592*b^2 +
    481043677184*b*c +
    297983878065779*b +
    18778072811188*c +
    1349778213513279
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    14831299527522068996*a +
    12065537511129088*b^2 +
    24131075022258176*b*c +
    14831299527522068996*b +
    883601378615600452*c +
    67126455198416893896
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035932906197042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239237968032520*a*b +
    42985986833672287212*a*c +
    3307868994650517369360*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149968622704944*b +
    161161705128390097350*c +
    7755243581683716758712
def conductorHi (a b c : ℕ) : ℕ :=
    1242959799564*a^3 +
    3728879398692*a^2*b +
    3728879398692*a^2*c +
    298407653079210*a^2 +
    3728879398692*a*b^2 +
    7457758797384*a*b*c +
    596815306158420*a*b +
    72802976944176*a*c +
    3446652178597608*a +
    18466977615192*b^2 +
    36933955230384*b*c +
    2341804994336304*b +
    245755677479328*c +
    9105841532376864
def slopeHi (a b : ℕ) : ℕ :=
    760284120838844196*a^2 +
    1520568241677688392*a*b +
    43013973771174489744*a +
    14559184820520708048*b +
    161237233498848064140
def interceptHi (a b : ℕ) : ℕ :=
    253428040279614732*a^3 +
    760284120838844196*a^2*b +
    315798877977693516696*a^2 +
    760284120838844196*a*b^2 +
    631296733517377913796*a*b +
    3309031422975064922640*a +
    7282138054556414232*b^2 +
    2300631986087458889859*b +
    7757818228452992100102
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G1

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G2
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source2,source2,source2]
def scale : ℕ := 21
def denominator : ℕ := 22126734
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    48233915486690
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280095636097083200*b +
    2273651471762231210
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778511959627358*b +
    121939515288971022438*c +
    4318407598621324060374
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    617762568719450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280095636097083200*b +
    280095636097083200*c +
    30697532167818317900
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778511959627358*b +
    121939515288971022438*c +
    4318407598621324060374
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    269722273014813*b +
    18769487660769*c +
    953539468824692
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12065537511129088*b^2 +
    24131075022258176*b*c +
    13413584371745410572*b +
    883170713129981736*c +
    47366298541628284388
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778511959627358*b +
    121939515288971022438*c +
    4318407598621324060374
def fullSlackLo (b c : ℕ) : ℕ :=
    1324084447260960*b^2 +
    2648168894521920*b*c +
    302000305580000370*b +
    24299010856385370*c +
    860190483763853760
def fullSlackHi (a b c : ℕ) : ℕ :=
    50509586104320*a^3 +
    151528758312960*a^2*b +
    151528758312960*a^2*c +
    57045754021945290*a^2 +
    151528758312960*a*b^2 +
    303057516625920*a*b*c +
    114091508043890580*a*b +
    8767102574348580*a*c +
    597391752403901070*a +
    1450358412521760*b^2 +
    2900716825043520*b*c +
    415864520101069830*b +
    32838819907912830*c +
    1400536481375106180
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    14738098216500*b^2 +
    29476196433000*b*c +
    1592100853456968*b +
    179345146500504*c +
    5408192047640274
def slopeLo (b : ℕ) : ℕ :=
    13292043376162834824*b +
    121989746316346731261
def interceptLo (b : ℕ) : ℕ :=
    6648567332377477620*b^2 +
    1516064581016149206960*b +
    4319832987369676682322
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19611314095841*a +
    5944381276688*b +
    67484444989635
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    925400094418933544*a +
    298193942363776832*b +
    3180953167863129810
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393759042911010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471347421493792*a*b +
    43981906407540296172*a*c +
    2999020156495354842768*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369402484856770*b +
    164783268342922143330*c +
    7031051085836975842332
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    270203316691997*a +
    5944381276688*b +
    5944381276688*c +
    887605100818551
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    13437715446767668748*a +
    298193942363776832*b +
    298193942363776832*c +
    44117149216267951704
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393759042911010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471347421493792*a*b +
    43981906407540296172*a*c +
    2999020156495354842768*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369402484856770*b +
    164783268342922143330*c +
    7031051085836975842332
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    270203316691997*a +
    240521838592*b^2 +
    481043677184*b*c +
    270203316691997*b +
    19250531337953*c +
    1223502263678097
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    13437715446767668748*a +
    12065537511129088*b^2 +
    24131075022258176*b*c +
    13437715446767668748*b +
    907301788152239912*c +
    60791948450884824048
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393759042911010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471347421493792*a*b +
    43981906407540296172*a*c +
    2999020156495354842768*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369402484856770*b +
    164783268342922143330*c +
    7031051085836975842332
def conductorHi (a b c : ℕ) : ℕ :=
    1242959799564*a^3 +
    3728879398692*a^2*b +
    3728879398692*a^2*c +
    272304700725942*a^2 +
    3728879398692*a*b^2 +
    7457758797384*a*b*c +
    544609401451884*a*b +
    73690832466396*a*c +
    3133416750358392*a +
    18466977615192*b^2 +
    36933955230384*b*c +
    2132981375510160*b +
    249307099568208*c +
    8270547057072288
def slopeHi (a b : ℕ) : ℕ :=
    760284120838844196*a^2 +
    1520568241677688392*a*b +
    44010044871488692764*a +
    14559184820520708048*b +
    164859364937553337845
def interceptHi (a b : ℕ) : ℕ :=
    253428040279614732*a^3 +
    760284120838844196*a^2*b +
    286501477575240213996*a^2 +
    760284120838844196*a*b^2 +
    572728207398241358400*a*b +
    3000097201024030784958*a +
    7282138054556414232*b^2 +
    2087652362164108479180*b +
    7033428708194500014384
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G2

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G3
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source3,source3,source3]
def scale : ℕ := 18
def denominator : ℕ := 16256376
def gLo0 (b c : ℕ) : ℕ :=
    4569960546736*b +
    40915071143710
def identitySlackLo0 (b c : ℕ) : ℕ :=
    229247500866464704*b +
    1927359630528423340
def helperSlackLo0 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792795802316072*b +
    88626013219367489952*c +
    4063930875261358050654
def gLo1 (b c : ℕ) : ℕ :=
    4569960546736*b +
    4569960546736*c +
    677017586556770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    229247500866464704*b +
    229247500866464704*c +
    33711702215384520080
def helperSlackLo1 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792795802316072*b +
    88626013219367489952*c +
    4063930875261358050654
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    296214311824897*b +
    16020638205407*c +
    1047860014200836
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10341889295253504*b^2 +
    20683778590507008*b*c +
    14759211539724417028*b +
    753617695606178708*c +
    52164516575947681304
def helperSlackLo2 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792795802316072*b +
    88626013219367489952*c +
    4063930875261358050654
def fullSlackLo (b c : ℕ) : ℕ :=
    933920149417920*b^2 +
    1867840298835840*b*c +
    283464093505168260*b +
    17661043233612540*c +
    809570949151648320
def fullSlackHi (a b c : ℕ) : ℕ :=
    37109083668480*a^3 +
    111327251005440*a^2*b +
    111327251005440*a^2*c +
    53615448797829300*a^2 +
    111327251005440*a*b^2 +
    222654502010880*a*b*c +
    107230897595658600*a*b +
    6416838718144920*a*c +
    562327314489010620*a +
    1026692858589120*b^2 +
    2053385717178240*b*c +
    390527999941203180*b +
    23910890792133780*c +
    1318282814276598600
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    12429717209064*b^2 +
    24859434418128*b*c +
    1730428982245692*b +
    152532148156308*c +
    5917821445231470
def slopeLo (b : ℕ) : ℕ :=
    9374799360057002928*b +
    88657056356040588888
def interceptLo (b : ℕ) : ℕ :=
    4688935972650322056*b^2 +
    1422887438097636255648*b +
    4065036368915279597310
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    16742203721183*a +
    4879202910640*b +
    57348030928125
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    789814308139565972*a +
    244760334809344960*b +
    2701661025823959360
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603772722285218*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190005429527668*a*b +
    32192135683147694556*a*c +
    2822771716263189900468*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923564671757140*b +
    119981686963996044324*c +
    6617563583274253106136
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    296626634976769*a +
    4879202910640*b +
    4879202910640*c +
    973334977596771
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    20683778590507008*a*c +
    14779895318314924036*a +
    244760334809344960*b +
    244760334809344960*c +
    48476084620855414164
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603772722285218*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190005429527668*a*b +
    32192135683147694556*a*c +
    2822771716263189900468*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923564671757140*b +
    119981686963996044324*c +
    6617563583274253106136
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    296626634976769*a +
    206161575936*b^2 +
    412323151872*b*c +
    296626634976769*b +
    16432961357279*c +
    1344280487601669
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10341889295253504*a^2 +
    20683778590507008*a*b +
    20683778590507008*a*c +
    14779895318314924036*a +
    10341889295253504*b^2 +
    20683778590507008*b*c +
    14779895318314924036*b +
    774301474196685716*c +
    66934070004967351836
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603772722285218*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190005429527668*a*b +
    32192135683147694556*a*c +
    2822771716263189900468*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923564671757140*b +
    119981686963996044324*c +
    6617563583274253106136
def conductorHi (a b c : ℕ) : ℕ :=
    1065394113912*a^3 +
    3196182341736*a^2*b +
    3196182341736*a^2*c +
    294501172772718*a^2 +
    3196182341736*a*b^2 +
    6392364683472*a*b*c +
    589002345545436*a*b +
    63036734182308*a*c +
    3418951508970120*a +
    15625899550800*b^2 +
    31251799101600*b*c +
    2316235145449392*b +
    212372699996880*c +
    9043337175542784
def slopeHi (a b : ℕ) : ℕ :=
    558576545377036392*a^2 +
    1117153090754072784*a*b +
    32209535868756738732*a +
    10305761334412844160*b +
    120028727584319133852
def interceptHi (a b : ℕ) : ℕ :=
    186192181792345464*a^3 +
    558576545377036392*a^2*b +
    269232474980920269834*a^2 +
    558576545377036392*a*b^2 +
    538245994865565413556*a*b +
    2823596669386350536796*a +
    5154416959828242672*b^2 +
    1960295568322723475436*b +
    6619400561545096358088
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G3
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 216
def denominator : ℕ := 2340918144
def gLo0 (b c : ℕ) : ℕ :=
    55123001676891*b +
    475020311572550
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2765190256119560124*b +
    22327670929829657000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    677767242150697505598*b^2 +
    1340242490172386980044*b*c +
    158047503411866675476500*b +
    12455799148799497205316*c +
    439483069414511293968162
def gLo1 (b c : ℕ) : ℕ :=
    55123001676891*b +
    53705626096596*c +
    5991631187983990
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2765190256119560124*b +
    2694089027509641744*c +
    297561690954237391960
def helperSlackLo1 (b c : ℕ) : ℕ :=
    677517160429997666622*b^2 +
    1339992408451687141068*b*c +
    158046543399864614629140*b +
    12454090256686691809476*c +
    439484491859661111037986
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2825190268278957*b +
    188845957072176*c +
    9513062221596442
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124102671543042048*b^2 +
    248205343086084096*b*c +
    140521846234029005988*b +
    8872769398610340384*c +
    472409255167087246888
def helperSlackLo2 (b c : ℕ) : ℕ :=
    677364867074443277502*b^2 +
    1339840115096132751948*b*c +
    158043823545267924614100*b +
    12453275887792427162628*c +
    439474696509502929320226
def fullSlackLo (b c : ℕ) : ℕ :=
    135096807766867920*b^2 +
    267132084280298640*b*c +
    31487290267311285840*b +
    2481773979561703200*c +
    87528528546162495840
def fullSlackHi (a b c : ℕ) : ℕ :=
    5343708048261120*a^3 +
    16031124144783360*a^2*b +
    16031124144783360*a^2*c +
    5693482732944867840*a^2 +
    16031124144783360*a*b^2 +
    32062248289566720*a*b*c +
    11838643376813503920*a*b +
    901165342053870720*a*c +
    60172825225513361760*a +
    148456077887520720*b^2 +
    293850624521604240*b*c +
    43301886917138979840*b +
    3358892594629764000*c +
    142007870957193720000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    1451643202179918*b^2 +
    2903286404359836*b*c +
    184628620425776868*b +
    17600977879243812*c +
    630015332286033666
def slopeLo (b : ℕ) : ℕ :=
    1340891740793434638924*b +
    12460226878643548201668
def interceptLo (b : ℕ) : ℕ :=
    678416492771745164478*b^2 +
    158086082877690579359508*b +
    439659811669917711124386
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    193725075047368*a +
    58833910043739*b +
    665034459378702
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    9117525472717871872*a +
    2951344263434123196*b +
    31259041448419169448
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26609655264958841184*a^3 +
    80030954876980239648*a^2*b +
    80232943959083955744*a^2*c +
    28586967200198944915842*a^2 +
    80232943959083955744*a*b^2 +
    160667877000271627584*a*b*c +
    59419456764963133320468*a*b +
    4521512652159015000900*a*c +
    302126749298877628348344*a +
    744594425729108789598*b^2 +
    1474098846411313264140*b*c +
    217346711736258261895176*b +
    16856861371304861588328*c +
    713022649238588493604536
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2621028002155232*a +
    58833910043739*b +
    57416534463444*c +
    8608948262898006
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    248205343086084096*a*c +
    130280250316198465088*a +
    2951344263434123196*b +
    2880243034824204816*c +
    427655786316307497624
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26532707043205044576*a^3 +
    79877058433472646432*a^2*b +
    80155995737330159136*a^2*c +
    28586278048504280039298*a^2 +
    80155995737330159136*a*b^2 +
    160590928778517830976*a*b*c +
    59418440583326014808340*a*b +
    4520557211641059889476*a*c +
    302125514561199367591608*a +
    744267395786655154014*b^2 +
    1473771816468859628556*b*c +
    217344889439062590128904*b +
    16854273986895854877672*c +
    713023449149532960997560
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2621028002155232*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2830138146101421*b +
    193793834894640*c +
    12131616284840442
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    248205343086084096*a*c +
    130280250316198465088*a +
    124102671543042048*b^2 +
    248205343086084096*b*c +
    140770051577115090084*b +
    9120974741696424480*c +
    602565402811742669928
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26484614404608921696*a^3 +
    79780873156280400672*a^2*b +
    80107903098734036256*a^2*c +
    28585065823317927494658*a^2 +
    80107903098734036256*a*b^2 +
    160542836139921708096*a*b*c +
    59417027972145511751700*a*b +
    4520049032698740772164*a*c +
    302117137443514417870008*a +
    744067009792504642014*b^2 +
    1473571430474709116556*b*c +
    217340853158562589302984*b +
    16852999531697867236392*c +
    713006440814237585979960
def conductorHi (a b c : ℕ) : ℕ :=
    123585717213792*a^3 +
    370757151641376*a^2*b +
    370757151641376*a^2*c +
    31472081785229058*a^2 +
    370757151641376*a*b^2 +
    741514303282752*a*b*c +
    62944163570458116*a*b +
    7268282721613764*a*c +
    364317723963659160*a +
    1822400353821294*b^2 +
    3644800707642588*b*c +
    247202026844593608*b +
    24498503449216200*c +
    962984560181677560
def slopeHi (a b : ℕ) : ℕ :=
    80434933041187671840*a^2 +
    160869866082375343680*a*b +
    4524005454183091729476*a +
    1474950086114464639116*b +
    16863579914090885597160
def interceptHi (a b : ℕ) : ℕ :=
    26811644347062557280*a^3 +
    80434933041187671840*a^2*b +
    28601907918366111569154*a^2 +
    80434933041187671840*a*b^2 +
    59435248722833451348756*a*b +
    302258007405507030455736*a +
    745445665432260164574*b^2 +
    217400679181788276374280*b +
    713315910871539249930936
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 378
def denominator : ℕ := 7169061816
def gLo0 (b c : ℕ) : ℕ :=
    97103071945692*b +
    862162941984460
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4871078501083693488*b +
    40622357856890904340
def helperSlackLo0 (b c : ℕ) : ℕ :=
    2087719876592441417178*b^2 +
    4191819108741119496744*b*c +
    468472780589902722734940*b +
    38768615579087371444788*c +
    1224863415946862106633774
def gLo1 (b c : ℕ) : ℕ :=
    97103071945692*b +
    97953497293869*c +
    9055043078043960
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4871078501083693488*b +
    4913739238249644516*c +
    448982813037362115240
def helperSlackLo1 (b c : ℕ) : ℕ :=
    2087263297104769475586*b^2 +
    4191362529253447555152*b*c +
    468471084291384384993048*b +
    38765414612580051192012*c +
    1224866289794289202756566
def gLo2 (b c : ℕ) : ℕ :=
    4329393094656*b^2 +
    8658786189312*b*c +
    5147547234039522*b +
    328496099063895*c +
    15475693921132356
def identitySlackLo2 (b c : ℕ) : ℕ :=
    217179675200323584*b^2 +
    434359350400647168*b*c +
    256119812276504543928*b +
    15427804727514209940*c +
    767915713154799334584
def helperSlackLo2 (b c : ℕ) : ℕ :=
    2086330500301998842226*b^2 +
    4190429732450676921792*b*c +
    468462417777742345972560*b +
    38759859560835732818736*c +
    1224846219734223851053782
def fullSlackLo (b c : ℕ) : ℕ :=
    416144929648114800*b^2 +
    835504467112338660*b*c +
    93335355554035676760*b +
    7724650123627477740*c +
    243950610851741833200
def fullSlackHi (a b c : ℕ) : ℕ :=
    16365105897799680*a^3 +
    49095317693399040*a^2*b +
    49095317693399040*a^2*c +
    15056052371138016000*a^2 +
    49095317693399040*a*b^2 +
    98190635386798080*a*b*c +
    34644701762989806600*a*b +
    2802323118941865540*a*c +
    163186823530862626320*a +
    457057694392614000*b^2 +
    917329996601337060*b*c +
    127906414215631440480*b +
    10453330141175300400*c +
    392081381761758554880
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    4688875681284402*b^2 +
    9377751362568804*b*c +
    548265466157300388*b +
    57054071355952068*c +
    1866704348318179086
def slopeLo (b : ℕ) : ℕ :=
    4193827076595504702240*b +
    38782246688896656059568
def interceptLo (b : ℕ) : ℕ :=
    2089727844446826622674*b^2 +
    468580920981398923588884*b +
    1225354150284373696257702
def gHi0 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    352247720082314*a +
    103597161587676*b +
    1207916539394646
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    217179675200323584*a^2 +
    434359350400647168*a*b +
    16619281044282180656*a +
    5196848013884178864*b +
    56915867731448456004
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    81492086028893745240*a^3 +
    245094849650623866264*a^2*b +
    245713441214566496808*a^2*c +
    75597267765378586685454*a^2 +
    245713441214566496808*a*b^2 +
    492045473993075624160*a*b*c +
    173880581837879118701988*a*b +
    14060237442358442282424*a*c +
    819358611192488706475536*a +
    2292378176641197856770*b^2 +
    4601754300402575006472*b*c +
    641985101528191607167848*b +
    52459973530291636827588*c +
    1968624139924785139592328
def gHi1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3957106279299264*a +
    103597161587676*b +
    104447586935853*c +
    13005655234671096
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    217179675200323584*a^2 +
    434359350400647168*a*b +
    434359350400647168*a*c +
    196402532222914241616*a +
    5196848013884178864*b +
    5239508751050129892*c +
    645059574090551727864
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    81344802323193118920*a^3 +
    244800282239222613624*a^2*b +
    245566157508865870488*a^2*c +
    75595941321777732163878*a^2 +
    245566157508865870488*a*b^2 +
    491898190287374997840*a*b*c +
    173878651531084891612500*a*b +
    14058416033677328858280*a*c +
    819356226169823535819816*a +
    2291774313447825288858*b^2 +
    4601150437209202438560*b*c +
    641981769490290443589108*b +
    52455098438808903776988*c +
    1968625807909442218954656
def gHi2 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3957106279299264*a +
    4329393094656*b^2 +
    8658786189312*b*c +
    5156206020228834*b +
    337154885253207*c +
    19428470807336964
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    217179675200323584*a^2 +
    434359350400647168*a*b +
    434359350400647168*a*c +
    196402532222914241616*a +
    217179675200323584*b^2 +
    434359350400647168*b*c +
    256554171626905191096*b +
    15862164077914857108*c +
    964101065702513252616
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    81050234911791866280*a^3 +
    244211147416420108344*a^2*b +
    245271590097464617848*a^2*c +
    75591422840970481854006*a^2 +
    245271590097464617848*a*b^2 +
    491603622875973745200*a*b*c +
    173872905686063469416628*a*b +
    14055097240467643387896*a*c +
    819333241535926710849096*a +
    2290546949233653402858*b^2 +
    4599923072995030552560*b*c +
    641967946266449784878028*b +
    52446519161266301185968*c +
    1968586977128875891338384
def conductorHi (a b c : ℕ) : ℕ :=
    395261216261352*a^3 +
    1185783648784056*a^2*b +
    1185783648784056*a^2*c +
    93587686991555382*a^2 +
    1185783648784056*a*b^2 +
    2371567297568112*a*b*c +
    187175373983110764*a*b +
    23438242382661324*a*c +
    1080364032542438568*a +
    5874659330068458*b^2 +
    11749318660136916*b*c +
    734255056491627096*b +
    79306530089829336*c +
    2853875955085323624
def slopeHi (a b : ℕ) : ℕ :=
    246332032778509127352*a^2 +
    492664065557018254704*a*b +
    14067881467470890638776*a +
    4604380859820902842512*b +
    52480630073649427168176
def interceptHi (a b : ℕ) : ℕ :=
    82110677592836375784*a^3 +
    246332032778509127352*a^2*b +
    75639331803209305528134*a^2 +
    246332032778509127352*a*b^2 +
    173925272435128165380708*a*b +
    819724637764408551917904*a +
    2295004736059525692810*b^2 +
    642136695333808969439424*b +
    1969439455387949798446488
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 27
def denominator : ℕ := 36576846
def gLo0 (b c : ℕ) : ℕ :=
    7138415936163*b +
    60552249349760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    358091497021680732*b +
    2849887038894392990
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944558962297586*b +
    196966484374269198726*c +
    6656751314891549866638
def gLo1 (b c : ℕ) : ℕ :=
    7138415936163*b +
    7138415936163*c +
    740894169953600
def identitySlackLo1 (b c : ℕ) : ℕ :=
    358091497021680732*b +
    358091497021680732*c +
    36790903146578455100
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944558962297586*b +
    196966484374269198726*c +
    6656751314891549866638
def gLo2 (b c : ℕ) : ℕ :=
    309242363904*b^2 +
    618484727808*b*c +
    323324839032829*b +
    23511252928669*c +
    1142799052169204
def identitySlackLo2 (b c : ℕ) : ℕ :=
    15512833942880256*b^2 +
    31025667885760512*b*c +
    16069142427253259836*b +
    1104356092918964656*c +
    56726871888381365756
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944558962297586*b +
    196966484374269198726*c +
    6656751314891549866638
def fullSlackLo (b c : ℕ) : ℕ :=
    2177858617526250*b^2 +
    4355717235052500*b*c +
    465789337835530230*b +
    39247966802185110*c +
    1325750788493742600
def fullSlackHi (a b c : ℕ) : ℕ :=
    83495438254080*a^3 +
    250486314762240*a^2*b +
    250486314762240*a^2*c +
    87965670044896470*a^2 +
    250486314762240*a*b^2 +
    500972629524480*a*b*c +
    175931340089792940*a*b +
    14157246750927660*a*c +
    920725333558323570*a +
    2386597213161450*b^2 +
    4773194426322900*b*c +
    641344947816169890*b +
    53029483443959490*c +
    2158510450733149860
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    18910932470262*b^2 +
    37821864940524*b*c +
    1914569502273576*b +
    226933725637800*c +
    6490309702448178
def slopeLo (b : ℕ) : ℕ :=
    21865084031205868788*b +
    197071799760392489316
def interceptLo (b : ℕ) : ℕ :=
    10937877292697191776*b^2 +
    2338660699519149940662*b +
    6659602356867712889904
def gHi0 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    24593601202333*a +
    7602279482019*b +
    84681984646941
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    15512833942880256*a^2 +
    31025667885760512*a*b +
    1158651011719045552*a +
    381360747936001116*b +
    3985268681347393614
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568435212682352*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130659619469904*a*b +
    71018836786852913088*a*c +
    4622937700573202893794*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500702361812390*b +
    266104937381042544426*c +
    10838025632971504491444
def gHi1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    323943323760637*a +
    7602279482019*b +
    7602279482019*c +
    1064373627809085
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    15512833942880256*a^2 +
    31025667885760512*a*b +
    31025667885760512*a*c +
    16100168095139020348*a +
    381360747936001116*b +
    381360747936001116*c +
    52867801872451430520
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568435212682352*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130659619469904*a*b +
    71018836786852913088*a*c +
    4622937700573202893794*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500702361812390*b +
    266104937381042544426*c +
    10838025632971504491444
def gHi2 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    323943323760637*a +
    309242363904*b^2 +
    618484727808*b*c +
    323943323760637*b +
    24129737656477*c +
    1466433133565937
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    15512833942880256*a^2 +
    31025667885760512*a*b +
    31025667885760512*a*c +
    16100168095139020348*a +
    15512833942880256*b^2 +
    31025667885760512*b*c +
    16100168095139020348*b +
    1135381760804725168*c +
    72811527149577505848
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568435212682352*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130659619469904*a*b +
    71018836786852913088*a*c +
    4622937700573202893794*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500702361812390*b +
    266104937381042544426*c +
    10838025632971504491444
def conductorHi (a b c : ℕ) : ℕ :=
    1598091170868*a^3 +
    4794273512604*a^2*b +
    4794273512604*a^2*c +
    328061859538806*a^2 +
    4794273512604*a*b^2 +
    9588547025208*a*b*c +
    656123719077612*a*b +
    93578460199020*a*c +
    3764148468011928*a +
    23705205982866*b^2 +
    47410411965732*b*c +
    2565898947838584*b +
    315717912324216*c +
    9927994402092168
def slopeHi (a b : ℕ) : ℕ :=
    1256794829961575580*a^2 +
    2513589659923151160*a*b +
    71078050854239731272*a +
    23959743679232998956*b +
    266264657570693040912
def interceptHi (a b : ℕ) : ℕ :=
    418931609987191860*a^3 +
    1256794829961575580*a^2*b +
    441915502368386371068*a^2 +
    1256794829961575580*a*b^2 +
    883285453867697973216*a*b +
    4625099883814868639820*a +
    11985207116710756860*b^2 +
    3220060960342908734202*b +
    10842786733520019184308
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    227123608966120*b +
    1962085248063300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11393428720176443680*b +
    92587857795363943200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10788159601498425061506*b^2 +
    21513302885187504249732*b*c +
    2123003999515132327052556*b +
    196405984272909192954288*c +
    5775658061288921966157366
def gLo1 (b c : ℕ) : ℕ :=
    227123608966120*b +
    225611741680472*c +
    19948839528421450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11393428720176443680*b +
    11317587409659197408*c +
    989037212926766741800
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10784377501401421323906*b^2 +
    21509520785090500512132*b*c +
    2122970546070384750178956*b +
    196380006573609546997488*c +
    5775584891222098113030966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9983821590984960*b +
    748511705502288*c +
    32350456257847930
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482621500445163520*b^2 +
    965243000890327040*b*c +
    496157877019382783040*b +
    35213066559423400032*c +
    1604146072818940956520
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10782074299419271611906*b^2 +
    21507217583108350800132*b*c +
    2122948347211632699812556*b +
    196366357068099407264688*c +
    5775531339514190155571766
def fullSlackLo (b c : ℕ) : ℕ :=
    2150284328616144000*b^2 +
    4287868972032844800*b*c +
    422978269413765492000*b +
    39134288322621307200*c +
    1150372535717105988000
def fullSlackHi (a b c : ℕ) : ℕ :=
    80815337766912000*a^3 +
    242446013300736000*a^2*b +
    242446013300736000*a^2*c +
    73656361872509850000*a^2 +
    242446013300736000*a*b^2 +
    484892026601472000*a*b*c +
    158166985938918810000*a*b +
    14111499533404039200*a*c +
    783863459695751274000*a +
    2352322673033424000*b^2 +
    4691945660867404800*b*c +
    580781585716170510000*b +
    52882118219511554400*c +
    1860579632307222036000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    26093810124594306*b^2 +
    52187620249188612*b*c +
    2960971989623422956*b +
    317219339510597808*c +
    10073154870362318166
def slopeLo (b : ℕ) : ℕ :=
    21522200518108019452932*b +
    196465540239899281093488
def interceptLo (b : ℕ) : ℕ :=
    10797057234418940264706*b^2 +
    2123466459832360592156556*b +
    5777748893679478592080566
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    241554919281640*b +
    2744390349876990
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    37632214424709967720*a +
    12117360970844188960*b +
    129496136287352513160
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369802462603166537288742*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    793823106277328194326684*a*b +
    70803773427188919899448*a*c +
    3935504907420608450687544*a +
    11799109461508455794466*b^2 +
    23537966447586145370052*b*c +
    2915007950929864030991880*b +
    265387838995123042811976*c +
    9341357738247938488264488
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    241554919281640*b +
    240043051995992*c +
    28645297412075655
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    432302499937564186980*a +
    12117360970844188960*b +
    12041519660326942688*c +
    1420615776931609531020
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785154885575374587942*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    793800852736533257507484*a*b +
    70789275375337310497848*a*c +
    3935419098764961859237944*a +
    11794163638304681676066*b^2 +
    23533020624382371251652*b*c +
    2914954571390535058060680*b +
    265348526967078557834376*c +
    9341214903519952436008488
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    10003063338072320*b +
    767753452589648*c +
    41051724651674295
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    432302499937564186980*a +
    482621500445163520*b^2 +
    965243000890327040*b*c +
    497123120020273110080*b +
    36178309560313727072*c +
    2035965951256059979980
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369773707212064730610342*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    793786374534098732329884*a*b +
    70781105068433675694648*a*c +
    3935359511438806687429944*a +
    11791133109380800476066*b^2 +
    23529990095458490051652*b*c +
    2914919348983231945492680*b +
    265327434481606514786376*c +
    9341112484832458219230888
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    505408450261226742*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    1010816900522453484*a*b +
    129566017151511768*a*c +
    5830429466544967944*a +
    32606919474309666*b^2 +
    65213838948619332*b*c +
    3965275780796161080*b +
    440272247312394216*c +
    15400346923095964488
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    70837497156568304027448*a +
    23549627922885240227652*b +
    265478354849113935424776
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    369983069739869648101542*a^2 +
    1216455140244462521760*a*b^2 +
    794015374889330399997084*a*b +
    3937068608183686383820344*a +
    11810770936807550652066*b^2 +
    2915657152174337342457480*b +
    9344834428107248516162088
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G7
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    223343940752000*b +
    1957274690704500
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11203825443883328000*b +
    92346540996017100000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10628812564384132664706*b^2 +
    21353955800720917334532*b*c +
    2162637281798319047454156*b +
    196203663257892546483888*c +
    5826402928871624074518966
def gLo1 (b c : ℕ) : ℕ :=
    223343940752000*b +
    225611741680472*c +
    19944028971062650
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11203825443883328000*b +
    11317587409659197408*c +
    988795896127419898600
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10625078952749911026306*b^2 +
    21350222189086695696132*b*c +
    2162592448550985918754956*b +
    196177261284636042267888*c +
    5826271604597595749574966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    10301313720971040*b +
    748511705502288*c +
    32754543075987130
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482621500445163520*b^2 +
    965243000890327040*b*c +
    512084552228004500160*b +
    35213066559423400032*c +
    1624416683964075785320
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10622727262304979215106*b^2 +
    21347870498641763884932*b*c +
    2162581629494819420214156*b +
    196164036053082760794288*c +
    5826276207096892263933366
def fullSlackLo (b c : ℕ) : ℕ :=
    2118535115617536000*b^2 +
    4256119759034236800*b*c +
    430875163764730356000*b +
    39093879640807387200*c +
    1160474708339318148000
def fullSlackHi (a b c : ℕ) : ℕ :=
    80815337766912000*a^3 +
    242446013300736000*a^2*b +
    242446013300736000*a^2*c +
    73656361872509850000*a^2 +
    242446013300736000*a*b^2 +
    484892026601472000*a*b*c +
    160833919830801882000*a*b +
    14111499533404039200*a*c +
    787257789835613418000*a +
    2320573460034816000*b^2 +
    4660196447868796800*b*c +
    591345413959018446000*b +
    52841709537697634400*c +
    1874076135069296340000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    26046457830075906*b^2 +
    52092915660151812*b*c +
    2984648136882622956*b +
    318450499168076208*c +
    10156494908714702166
def slopeLo (b : ℕ) : ℕ :=
    21362853433641432537732*b +
    196263219224882634623088
def interceptLo (b : ℕ) : ℕ :=
    10637710197304647867906*b^2 +
    2163099742115547312558156*b +
    5828493761262180700442166
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    237775251067520*b +
    2739579792518190
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    37632214424709967720*a +
    11927757694551073280*b +
    129254819488005669960
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369806733565484101563942*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    807208406837909841501084*a*b +
    70803967854562993480248*a*c +
    3952577168309316732402744*a +
    11639762424394163397666*b^2 +
    23378619363119558454852*b*c +
    2968026533773632398567880*b +
    265185712407480469922376*c +
    9409170595757031314066088
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    237775251067520*b +
    240043051995992*c +
    28640486854716855
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    432302499937564186980*a +
    11927757694551073280*b +
    12041519660326942688*c +
    1420374460132262687820
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785158863168114133542*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    807181934800852862051484*a*b +
    70789275848860255681848*a*c +
    3952449854188127852121144*a +
    11634865089653171378466*b^2 +
    23373722028378566435652*b*c +
    2967957555935455831180680*b +
    265145782151627998288776*c +
    9408932368341023325890088
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    10320555468058400*b +
    767753452589648*c +
    41455811469813495
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    432302499937564186980*a +
    482621500445163520*b^2 +
    965243000890327040*b*c +
    513049795228894827200*b +
    36178309560313727072*c +
    2056236562401194808780
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369777978174382294885542*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    807171675094680379504284*a*b +
    70781299495807749275448*a*c +
    3952431772327514969145144*a +
    11631786072266508079266*b^2 +
    23370643010991903136452*b*c +
    2967937931827000313068680*b +
    265125307893963941896776*c +
    9408925342341551045032488
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    509386043000772342*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    1018772086001544684*a*b +
    130039540096695768*a*c +
    5878160579419515144*a +
    32559567179791266*b^2 +
    65119134359582532*b*c +
    3996907113534452280*b +
    441976929915056616*c +
    15527440481583350088
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    70837691583942377608248*a +
    23390280838418653312452*b +
    265276228261471362535176
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    369987340702187212376742*a^2 +
    1216455140244462521760*a*b^2 +
    807400675449912047171484*a*b +
    3954140869072394665535544*a +
    11651423899693258255266*b^2 +
    2968675735018105710033480*b +
    9412647285616341341963688
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    230903277180240*b +
    1996961420600300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11583031996469559360*b +
    94337386114510011200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10947603688046482638006*b^2 +
    21672747091596057325932*b*c +
    2012795416502645815421340*b +
    198547667234261671078512*c +
    5521658595539622708986310
def gLo1 (b c : ℕ) : ℕ :=
    230903277180240*b +
    225611741680472*c +
    19232075321503450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11583031996469559360*b +
    11317587409659197408*c +
    953081453250932189800
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10943409436015831057206*b^2 +
    21668552839565405745132*b*c +
    2012762624712061912166940*b +
    198518428685285018297712*c +
    5521598960227522266698310
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9348837331012800*b +
    753803241002056*c +
    30820707857292730
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482621500445163520*b^2 +
    965243000890327040*b*c +
    464304526602139348800*b +
    35478511146233761984*c +
    1527407774053489903720
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10941057745570899246006*b^2 +
    21666201149120473933932*b*c +
    2012731270791907194614940*b +
    198505470140277038369712*c +
    5521500905547355020199110
def fullSlackLo (b c : ℕ) : ℕ :=
    2182033541614752000*b^2 +
    4319618185031452800*b*c +
    401019345800972724000*b +
    39560594866526260800*c +
    1099781251009905156000
def fullSlackHi (a b c : ℕ) : ℕ :=
    80815337766912000*a^3 +
    242446013300736000*a^2*b +
    242446013300736000*a^2*c +
    70989427980626778000*a^2 +
    242446013300736000*a*b^2 +
    484892026601472000*a*b*c +
    150166184263269594000*a*b +
    14267070677097218400*a*c +
    752345040008497194000*a +
    2384071886032032000*b^2 +
    4723694873866012800*b*c +
    550821860427728526000*b +
    53463995907109687200*c +
    1781136861804650196000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    26213670620094006*b^2 +
    52427341240188012*b*c +
    2823786946889748540*b +
    322250994326122992*c +
    9591808615839460710
def slopeLo (b : ℕ) : ℕ :=
    21681644724516572529132*b +
    198607356544524409990512
def interceptLo (b : ℕ) : ℕ :=
    10956501320966997841206*b^2 +
    2013241475597338035470940*b +
    5523667430374974831722310
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    809965324278950*a +
    245334587495760*b +
    2792495361163410
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    38295825891735872600*a +
    12306964247137304640*b +
    131909276073524486040
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    356409437388107229487206*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    753668055365308195971612*a*b +
    71585210393289432845256*a*c +
    3777248171728560580435512*a +
    11958553548056513370966*b^2 +
    23697410653994698446252*b*c +
    2764644317005357521005592*b +
    268310958922576033882008*c +
    8942494562021650668642936
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8393397137383965*a +
    245334587495760*b +
    240043051995992*c +
    27611041075171575
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    416375824728942469860*a +
    12306964247137304640*b +
    12041519660326942688*c +
    1368733342047153261900
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401412015874457841120*a^3 +
    1208309078497069856160*a^2*b +
    1212382109370766188960*a^2*c +
    356391566325088980722406*a^2 +
    1212382109370766188960*a*b^2 +
    2428837249615228710720*a*b*c +
    753644680861764178947612*a*b +
    71568845535435742406856*a*c +
    3777167371308976472390712*a +
    11953050107530745111766*b^2 +
    23691907213468930187052*b*c +
    2764590769088219834083992*b +
    268266664704240807341208*c +
    8942370688164489250396536
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8393397137383965*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9368079078100160*b +
    773044988089416*c +
    39204484121133015
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    416375824728942469860*a +
    482621500445163520*b^2 +
    965243000890327040*b*c +
    465269769603029675840*b +
    36443754147124089024*c +
    1943300977281987210060
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400684688932726353120*a^3 +
    1206854424613606880160*a^2*b +
    1211654782429034700960*a^2*c +
    356376918413034718197606*a^2 +
    1211654782429034700960*a*b^2 +
    2428109922673497222720*a*b*c +
    753626953932323253123612*a*b +
    71560966159308800198856*a*c +
    3777076489734988712198712*a +
    11949971090144081812566*b^2 +
    23688828196082266887852*b*c +
    2764543142892507653683992*b +
    268246554110047616693208*c +
    8942195672495446774742136
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    482464369475281206*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    964928738950562412*a*b +
    131083421429353896*a*c +
    5555100497113621512*a +
    32726779969809366*b^2 +
    65453559939618732*b*c +
    3782202576490595592*b +
    446821306405761528*c +
    14666615779927706136
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    71618982611131599072456*a +
    23709072129293793303852*b +
    268401656608302359366808
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    356584080443888142098406*a^2 +
    1216455140244462521760*a*b^2 +
    753854359896388203440412*a*b +
    3778753725555138988464312*a +
    11970215023355608228566*b^2 +
    2765271152946372589215192*b +
    8945837071470178866450936
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 216
def denominator : ℕ := 2340918144
def gLo0 (b c : ℕ) : ℕ :=
    57674277721422*b +
    497165824473180
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2893172467617413208*b +
    23438578438976860320
def helperSlackLo0 (b c : ℕ) : ℕ :=
    705412122723948431916*b^2 +
    1392464875200549283512*b*c +
    137060163646697636618004*b +
    12745137084326426595312*c +
    378066895730787763784070
def gLo1 (b c : ℕ) : ℕ :=
    57674277721422*b +
    55973427025068*c +
    5137578772834220
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2893172467617413208*b +
    2807850993285511152*c +
    254719005600664329680
def helperSlackLo1 (b c : ℕ) : ℕ :=
    705134788508044123308*b^2 +
    1392187540984644974904*b*c +
    137058524392222360366740*b +
    12743203759863480574704*c +
    378065597594129568551430
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2462909069955555*b +
    188845957072176*c +
    8194670757388502
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124102671543042048*b^2 +
    248205343086084096*b*c +
    122348372201333868060*b +
    8872769398610340384*c +
    406273465756560144728
def helperSlackLo2 (b c : ℕ) : ℕ :=
    704982495152489734188*b^2 +
    1392035247629090585784*b*c +
    137056448177438881796244*b +
    12742389390969215927856*c +
    378059020444376703929862
def fullSlackLo (b c : ℕ) : ℕ :=
    140607564023054880*b^2 +
    277541290541985120*b*c +
    27305976512686016880*b +
    2539405187438063040*c +
    75295846944707983200
def fullSlackHi (a b c : ℕ) : ℕ :=
    5343708048261120*a^3 +
    16031124144783360*a^2*b +
    16031124144783360*a^2*c +
    4878707215363447680*a^2 +
    16031124144783360*a*b^2 +
    32062248289566720*a*b*c +
    10241340470853535440*a*b +
    919126325407368960*a*c +
    51621671469959915040*a +
    153966834143707680*b^2 +
    304259830783290720*b*c +
    37523270256553742400*b +
    3434484785859622080*c +
    122038811117767180800
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    1473040520265420*b^2 +
    2946081040530840*b*c +
    161077009701160260*b +
    17969793063174000*c +
    547370721569020518
def slopeLo (b : ℕ) : ℕ :=
    1393144584492707820216*b +
    12749708290585096751472
def interceptLo (b : ℕ) : ℕ :=
    706091832016106968620*b^2 +
    137094949127439508220244*b +
    378223906017377532672774
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    202040345118432*a +
    61385186088270*b +
    695495242350396
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    9534652680562726368*a +
    3079326474931976280*b +
    32787076165411227264
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26600036737239616608*a^3 +
    80011717821541790496*a^2*b +
    80223325431364731168*a^2*c +
    24495889585380374575422*a^2 +
    80223325431364731168*a*b^2 +
    160658258472552403008*a*b*c +
    51402107864369122975980*a*b +
    4611631787521216786656*a*c +
    259193458046979971475912*a +
    772229687774640491340*b^2 +
    1526311612911756343032*b*c +
    188342042307550651141344*b +
    17236328060721711988656*c +
    612764252299258157663856
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2243817114386056*a +
    61385186088270*b +
    59684335391916*c +
    7377684959979060
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    248205343086084096*a*c +
    111357843342145520224*a +
    3079326474931976280*b +
    2994005000600074224*c +
    365890693988681490480
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26513469987766595424*a^3 +
    79838584322595748128*a^2*b +
    80136758681891709984*a^2*c +
    24494900277482123842494*a^2 +
    80136758681891709984*a*b^2 +
    160571691723079381824*a*b*c +
    51400754655505494913260*a*b +
    4610549703042727867872*a*c +
    259189990938630660984264*a +
    771865786809263161548*b^2 +
    1525947711946379013240*b*c +
    188339222977710692869728*b +
    17233399218529750070448*c +
    612760389795399429651312
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2243817114386056*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2467856947778019*b +
    193793834894640*c +
    10436013932863326
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124102671543042048*a^2 +
    248205343086084096*a*b +
    248205343086084096*a*c +
    111357843342145520224*a +
    124102671543042048*b^2 +
    248205343086084096*b*c +
    122596577544419952156*b +
    9120974741696424480*c +
    517507206427162622904
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26465377349170472544*a^3 +
    79742399045403502368*a^2*b +
    80088666043295587104*a^2*c +
    24493922103136939095870*a^2 +
    80088666043295587104*a*b^2 +
    160523599084483258944*a*b*c +
    51399576095166159654636*a*b +
    4610041524100408750560*a*c +
    259183895817093517251144*a +
    771665400815112649548*b^2 +
    1525747325952228501240*b*c +
    188336064387865071286368*b +
    17232124763331762429168*c +
    612748647605816009920368
def conductorHi (a b c : ℕ) : ℕ :=
    123585717213792*a^3 +
    370757151641376*a^2*b +
    370757151641376*a^2*c +
    27532548452402622*a^2 +
    370757151641376*a*b^2 +
    741514303282752*a*b*c +
    55065096904805244*a*b +
    7362691358809824*a*c +
    317043323969741928*a +
    1843797671906796*b^2 +
    3687595343813592*b*c +
    215771349454324128*b +
    24961727270342448*c +
    837005082803573616
def slopeHi (a b : ℕ) : ℕ :=
    80434933041187671840*a^2 +
    160869866082375343680*a*b +
    4614219171746763240672*a +
    1527202929813737820408*b +
    17243275043596105658160
def interceptHi (a b : ℕ) : ℕ :=
    26811644347062557280*a^3 +
    80434933041187671840*a^2*b +
    24509495310038858907198*a^2 +
    80434933041187671840*a*b^2 +
    51416604905929588785132*a*b +
    259311011131709512366536*a +
    773121004676621968716*b^2 +
    188390901614633342671392*b +
    613025421553528806052080
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    804299443743210
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    37844797329441484440
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882708954581030949278*b^2 +
    3757053275717680215756*b*c +
    418730590443874058768340*b +
    34486527131241078222468*c +
    1119334564053736914715650
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8862743329077330
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    4584950017329294080*c +
    439586496426849378120
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    418729737053651632904340*b +
    34482036257577733475268*c +
    1119345681416735406917250
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14731795051764750
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234203077056715009980*b +
    14408742445097669280*c +
    730999103448265803000
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    418718765834371419507540*b +
    34477046645134291470468*c +
    1119311928250591474238850
def fullSlackLo (b c : ℕ) : ℕ :=
    375268910463522000*b^2 +
    748836970230690000*b*c +
    83420784481922658000*b +
    6871138710079716000*c +
    222915251098893132000
def fullSlackHi (a b c : ℕ) : ℕ :=
    14843633467392000*a^3 +
    44530900402176000*a^2*b +
    44530900402176000*a^2*c +
    14035913205256612800*a^2 +
    44530900402176000*a*b^2 +
    89061800804352000*a*b*c +
    31105803882669490800*a*b +
    2495980098289641600*a*c +
    150647610808810317600*a +
    412377994132002000*b^2 +
    823055137567650000*b*c +
    114459791900742676800*b +
    9300322344519885600*c +
    359526948475954420800
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    3938060860543278*b^2 +
    7876121721086556*b*c +
    493794310176693540*b +
    47471470009952868*c +
    1684392859911146850
def slopeLo (b : ℕ) : ℕ :=
    3758932451040602794956*b +
    34499082429680112342468
def interceptLo (b : ℕ) : ℕ :=
    1884588129903953528478*b^2 +
    418839568936501534933140*b +
    1119832680889670407157250
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    328418638459656*a +
    98056516739565*b +
    1126533203467506
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    15473960593093022784*a +
    4918907105723538660*b +
    53008499665653908184
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73888981466606811360*a^3 +
    222254743315995269280*a^2*b +
    222842542232170104480*a^2*c +
    70480173773551415043618*a^2 +
    222842542232170104480*a*b^2 +
    446272883380515044160*a*b*c +
    156125970424942000343316*a*b +
    12523457003250956983812*a*c +
    756455296499524673414136*a +
    2068313273533554743358*b^2 +
    4128849712538902639116*b*c +
    574522590887459600891976*b +
    46675426354219402151400*c +
    1805309098178214439238328
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3874125390125628*a +
    98056516739565*b +
    97584058212800*c +
    12730683840467598
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    192339962097067681392*a +
    4918907105723538660*b +
    4895206696186899200*c +
    631616200267036460472
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    70479066512388086586018*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    156124057166779977604116*a*b +
    12521021199928686353412*a*c +
    756457799310191661167736*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    574520198292930899911176*b +
    46668686704161660585000*c +
    1805323638586115373839928
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3874125390125628*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    315430388396160*c +
    18601797210371658
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    192339962097067681392*a +
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234616752628525150140*b +
    14822418016907809440*c +
    923132227759428414312
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    70473837049486636294818*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    156117714448355468912916*a*b +
    12518028768742964158212*a*c +
    756425924710359888575736*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    574503418717877245855176*b +
    46660971841858030401000*c +
    1805262973101715584844728
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    84180294890934498*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    168360589781868996*a*b +
    19586309726288772*a*c +
    974110601876431896*a +
    4939531327620558*b^2 +
    9879062655241116*b*c +
    661153429491485256*b +
    66056309269164360*c +
    2574656990385670008
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12530599651434330353412*a +
    4131316686778000053516*b +
    46694536501925634805800
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    70522482817559840835618*a^2 +
    223430341148344939680*a*b^2 +
    156170746443189523549716*a*b +
    756825834988824058012536*a +
    2070780247772652157758*b^2 +
    574675169800502250592776*b +
    1806136032258355065321528
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G11
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G12
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source23,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    38103347875692780120
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882851443711615301534*b^2 +
    3723060364136351206668*b*c +
    415192427706184265598228*b +
    34921690602697051626564*c +
    1101640197905858397001698
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    89509376827660*c +
    8666887321630770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    4490148379182736240*c +
    429761575669300142280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089976933843355934*b^2 +
    3722298897358579261068*b*c +
    415188747539911265867028*b +
    34916634195041135543364*c +
    1101640753271669902422498
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    314743261786960*c +
    14535939044318190
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234203077056715009980*b +
    14787948997683900640*c +
    721174182690716567160
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881168201360751000734*b^2 +
    3721377121785486905868*b*c +
    415178877513807120649428*b +
    34911241583996424032964*c +
    1101614397031619079270498
def fullSlackLo (b c : ℕ) : ℕ :=
    375268910463522000*b^2 +
    742033567445274000*b*c +
    82715702855115042000*b +
    6957727517586708000*c +
    219389843681864460000
def fullSlackHi (a b c : ℕ) : ℕ :=
    14843633467392000*a^3 +
    44530900402176000*a^2*b +
    44530900402176000*a^2*c +
    13725678038241643200*a^2 +
    44530900402176000*a*b^2 +
    89061800804352000*a*b*c +
    30795568715654521200*a*b +
    2531357792773804800*a*c +
    147770883251901050400*a +
    412377994132002000*b^2 +
    816251734782234000*b*c +
    113444475106920091200*b +
    9422288846511040800*c +
    353435048669031451200
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    3930484493420334*b^2 +
    7860968986840668*b*c +
    487203817825622628*b +
    47776418786651364*c +
    1661401900353628098
def slopeLo (b : ℕ) : ℕ :=
    3724797042752322310668*b +
    34933680367143514410564
def interceptLo (b : ℕ) : ℕ :=
    1884588122327586405534*b^2 +
    415298579422761167895828*b +
    1102127752744604902662498
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    15587722558868892192*a +
    4918907105723538660*b +
    53380812177681073272
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73942417731713614560*a^3 +
    222361615846208875680*a^2*b +
    222895978497276907680*a^2*c +
    68923743354114848120322*a^2 +
    222895978497276907680*a*b^2 +
    446326319645621847360*a*b*c +
    154569734845113011268564*a*b +
    12701477709937859827716*a*c +
    742019111705428523182584*a +
    2068509198929245898814*b^2 +
    4094910237222680433228*b*c +
    569428085697410605040712*b +
    47288557096097171596200*c +
    1774735031091941445019320
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    98056516739565*b +
    95694224105740*c +
    12448651397739102
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    188017007397584643888*a +
    4918907105723538660*b +
    4800405058040341360*c +
    617468324810004187128
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    68921289176077794613122*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    154566278737105205201364*a*b +
    12698578792250048659716*a*c +
    742012372719993910193784*a +
    2067507268958493338814*b^2 +
    4093908307251927873228*b*c +
    569421430349515760471112*b +
    47280842233946424959400*c +
    1774731061187162410344120
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    322989724824400*c +
    18319764767643162
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    188017007397584643888*a +
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234616752628525150140*b +
    15201624569494040800*c +
    908984352302396140968
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73408055080645582560*a^3 +
    221292890544072811680*a^2*b +
    222361615846208875680*a^2*c +
    68916312483334666385922*a^2 +
    222361615846208875680*a*b^2 +
    445791956994553815360*a*b*c +
    154560086369330897201364*a*b +
    12695314726682726093316*a*c +
    741984895566298619470584*a +
    2066291593927313566014*b^2 +
    4092692632220748100428*b*c +
    569405955754553482088712*b +
    47272479456792478300200*c +
    1774681910586701337278520
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    83086930410504642*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    166173860821009284*a*b +
    19698061141352196*a*c +
    960990228111273624*a +
    4931954960497614*b^2 +
    9863909920995228*b*c +
    652376208179554632*b +
    66473009460926280*c +
    2539639021543422840
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12708157243755692659716*a +
    4097181278489719569228*b +
    47306692031710399180200
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    68964705481249548862722*a^2 +
    223430341148344939680*a*b^2 +
    154612968013514751146964*a*b +
    742380408398626307038584*a +
    2070780240196285034814*b^2 +
    569576401857087111152712*b +
    1775543454859402101825720
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G12

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G13
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source25,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    38103347875692780120
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882784660218305427134*b^2 +
    3757128985616661200268*b*c +
    415191809065419348255828*b +
    34580026949459771111364*c +
    1101638771605333447098498
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8666887321630770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    4584950017329294080*c +
    429761575669300142280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882098894816101452734*b^2 +
    3756443220214457225868*b*c +
    415189746275957588958228*b +
    34575226590676080824964*c +
    1101645513432348194231298
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14535939044318190
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234203077056715009980*b +
    14408742445097669280*c +
    721174182690716567160
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881177119243009097534*b^2 +
    3755521444641364870668*b*c +
    415179876249853443740628*b +
    34569833979631369314564*c +
    1101619157192297371079298
def fullSlackLo (b c : ℕ) : ℕ :=
    375268910463522000*b^2 +
    748836970230690000*b*c +
    82715702894948898000*b +
    6889693489732548000*c +
    219389843403027468000
def fullSlackHi (a b c : ℕ) : ℕ :=
    14843633467392000*a^3 +
    44530900402176000*a^2*b +
    44530900402176000*a^2*c +
    13725678038241643200*a^2 +
    44530900402176000*a*b^2 +
    89061800804352000*a*b*c +
    30795568715654521200*a*b +
    2504144181632140800*a*c +
    147770883132399482400*a +
    412377994132002000*b^2 +
    823055137567650000*b*c +
    113444475146753947200*b +
    9327041207515216800*c +
    353435048270692891200
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    3942322567049934*b^2 +
    7884645134099868*b*c +
    490163336233022628*b +
    47539657314059364*c +
    1671641834043232098
def slopeLo (b : ℕ) : ℕ :=
    3758941365608200275468*b +
    34592272762778459692164
def interceptLo (b : ℕ) : ℕ :=
    1884597040209844502334*b^2 +
    415299578158807490987028*b +
    1102132512905283194471298
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    15587722558868892192*a +
    4918907105723538660*b +
    53380812177681073272
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73915699599160212960*a^3 +
    222308179581102072480*a^2*b +
    222869260364723506080*a^2*c +
    68923346468408722892322*a^2 +
    222869260364723506080*a*b^2 +
    446299601513068445760*a*b*c +
    154569244931303967948564*a*b +
    12564691126442038867716*a*c +
    742017197714255261902584*a +
    2068415697303382622814*b^2 +
    4128952140570437025228*b*c +
    569427030579101751181512*b +
    46810133577496623522600*c +
    1774732060967816805662520
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    98056516739565*b +
    97584058212800*c +
    12448651397739102
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    188017007397584643888*a +
    4918907105723538660*b +
    4895206696186899200*c +
    617468324810004187128
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    68921628091117823180322*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    154566627043550437049364*a*b +
    12562010406870721267716*a*c +
    742015696694789409396984*a +
    2067516186840751435614*b^2 +
    4128052630107805838028*b*c +
    569422777392007315410312*b +
    46802866244202042849000*c +
    1774738806407596172788920
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    315430388396160*c +
    18319764767643162
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    188017007397584643888*a +
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234616752628525150140*b +
    14822418016907809440*c +
    908984352302396140968
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73408055080645582560*a^3 +
    221292890544072811680*a^2*b +
    222361615846208875680*a^2*c +
    68916651398374694953122*a^2 +
    222361615846208875680*a*b^2 +
    445791956994553815360*a*b*c +
    154560434675776129049364*a*b +
    12558746341303398701316*a*c +
    741988219541094118673784*a +
    2066300511809571662814*b^2 +
    4126836955076626065228*b*c +
    569407302797045037027912*b +
    46794503467048096189800*c +
    1774689655807135099723320
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    83572291429318242*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    167144582858636484*a*b +
    19603356552315396*a*c +
    966814560337036824*a +
    4943793034127214*b^2 +
    9887586068254428*b*c +
    656306448624581832*b +
    66141543399297480*c +
    2555217926439976440
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12571588858376365267716*a +
    4131325601345597534028*b +
    46828716041966017069800
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    68965044396289577429922*a^2 +
    223430341148344939680*a*b^2 +
    154613316319959982994964*a*b +
    742383732373421806241784*a +
    2070789158078543131614*b^2 +
    569577748899578666091912*b +
    1775551200079835864270520
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G13

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G14
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source25,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    37974072602567132280
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882775749912414453278*b^2 +
    3757120071049063719756*b*c +
    417194329365211525205652*b +
    34533409509268229724804*c +
    1111651592598277217139042
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8777700589001850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    4584950017329294080*c +
    435320412413702999400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    417192266575749765908052*b +
    34528609150484539438404*c +
    1111658334425291964271842
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14646752311689270
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234203077056715009980*b +
    14408742445097669280*c +
    726733019435119424280
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    417182079088357785624852*b +
    34523595046419590148804*c +
    1111628498342170474486242
def fullSlackLo (b c : ℕ) : ℕ :=
    375268910463522000*b^2 +
    748836970230690000*b*c +
    83114630617650930000*b +
    6880416099906132000*c +
    221384481897036060000
def fullSlackHi (a b c : ℕ) : ℕ :=
    14843633467392000*a^3 +
    44530900402176000*a^2*b +
    44530900402176000*a^2*c +
    13901205830105376000*a^2 +
    44530900402176000*a*b^2 +
    89061800804352000*a*b*c +
    30971096507518254000*a*b +
    2500062139960891200*a*c +
    149398505358313788000*a +
    412377994132002000*b^2 +
    823055137567650000*b*c +
    114018930661319712000*b +
    9313681776017551200*c +
    356881781198752056000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    3938060860543278*b^2 +
    7876121721086556*b*c +
    491245809685713252*b +
    47497040248992804*c +
    1675473108192715842
def slopeLo (b : ℕ) : ℕ :=
    3758932451040602794956*b +
    34545655322586918305604
def interceptLo (b : ℕ) : ℕ :=
    1884588129903953528478*b^2 +
    417302098458599667936852*b +
    1112145333898226964511842
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    15530841575980957488*a +
    4918907105723538660*b +
    53194655921667490728
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73915699599160212960*a^3 +
    222308179581102072480*a^2*b +
    222869260364723506080*a^2*c +
    69804404942370758784450*a^2 +
    222869260364723506080*a*b^2 +
    446299601513068445760*a*b*c +
    155450294682475199159700*a*b +
    12544192069948929176964*a*c +
    750187171170453187867320*a +
    2068406786997491648958*b^2 +
    4128943226002839544716*b*c +
    572310600630065159342472*b +
    46743017080811972445288*c +
    1792033796942996465775672
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    98056516739565*b +
    97584058212800*c +
    12608222385072330
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    190462889661765836160*a +
    4918907105723538660*b +
    4895206696186899200*c +
    625473043818588236520
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    69802686565079859072450*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    155447676794721668260500*a*b +
    12541511350377611576964*a*c +
    750185670150987335361720*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    572306347442970723571272*b +
    46735749747517391771688*c +
    1792040542382775832902072
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    315430388396160*c +
    18479335754976390
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    190462889661765836160*a +
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234616752628525150140*b +
    14822418016907809440*c +
    916989071310980190360
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    69797742095592311731650*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    155441619069711062519700*a*b +
    12538510013147704914564*a*c +
    750156573711468208977720*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    572290636593219205579272*b +
    46728001487548069835688*c +
    1791986287148297230057272
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    83755544809104450*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    167511089618208900*a*b +
    19594833139302084*a*c +
    969013600894471320*a +
    4939531327620558*b^2 +
    9879062655241116*b*c +
    657755428836844872*b +
    66090402921217608*c +
    2561064987767108472
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12551089801883255576964*a +
    4131316686778000053516*b +
    46761599545281365992488
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    69846102870251613322050*a^2 +
    223430341148344939680*a*b^2 +
    155494366071131214206100*a*b +
    750553705829619732206520*a +
    2070780247772652157758*b^2 +
    572461318950542074252872*b +
    1792852936055015524383672
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G14

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G15
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source21,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    37974072602567132280
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882708954581030949278*b^2 +
    3757053275717680215756*b*c +
    417193709469570969269652*b +
    34533100024147884185604*c +
    1111650162024486523942242
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8777700589001850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4608650426865933540*b +
    4584950017329294080*c +
    435320412413702999400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    417192856079348543405652*b +
    34528609150484539438404*c +
    1111661279387485016143842
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14646752311689270
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234203077056715009980*b +
    14408742445097669280*c +
    726733019435119424280
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    417182668591956563122452*b +
    34523595046419590148804*c +
    1111631443304363526358242
def fullSlackLo (b c : ℕ) : ℕ :=
    375268910463522000*b^2 +
    748836970230690000*b*c +
    83114630617650930000*b +
    6880416099906132000*c +
    221384481897036060000
def fullSlackHi (a b c : ℕ) : ℕ :=
    14843633467392000*a^3 +
    44530900402176000*a^2*b +
    44530900402176000*a^2*c +
    13901205830105376000*a^2 +
    44530900402176000*a*b^2 +
    89061800804352000*a*b*c +
    30971096507518254000*a*b +
    2500062139960891200*a*c +
    149398505358313788000*a +
    412377994132002000*b^2 +
    823055137567650000*b*c +
    114018930661319712000*b +
    9313681776017551200*c +
    356881781198752056000
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    3938060860543278*b^2 +
    7876121721086556*b*c +
    492950492288375652*b +
    47497040248992804*c +
    1681439497302034242
def slopeLo (b : ℕ) : ℕ :=
    3758932451040602794956*b +
    34545655322586918305604
def interceptLo (b : ℕ) : ℕ :=
    1884588129903953528478*b^2 +
    417302687962198445434452*b +
    1112148278860420016383842
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    15530841575980957488*a +
    4918907105723538660*b +
    53194655921667490728
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73888981466606811360*a^3 +
    222254743315995269280*a^2*b +
    222842542232170104480*a^2*c +
    69804007855417381853250*a^2 +
    222842542232170104480*a*b^2 +
    446272883380515044160*a*b*c +
    155449804366171652433300*a*b +
    12543947153699882207364*a*c +
    750185254764432407716920*a +
    2068313273533554743358*b^2 +
    4128849712538902639116*b*c +
    572309543854386163483272*b +
    46742489397575133338088*c +
    1792030820332005815958072
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    98056516739565*b +
    97584058212800*c +
    12608222385072330
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    190462889661765836160*a +
    4918907105723538660*b +
    4895206696186899200*c +
    625473043818588236520
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    69802900594254053395650*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    155447891108009629694100*a*b +
    12541511350377611576964*a*c +
    750187757575099395470520*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    572307151259857462502472*b +
    46735749747517391771688*c +
    1792045360739906750559672
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    315430388396160*c +
    18479335754976390
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206837785905070080*a^2 +
    413675571810140160*a*b +
    413675571810140160*a*c +
    190462889661765836160*a +
    206837785905070080*b^2 +
    413675571810140160*b*c +
    234616752628525150140*b +
    14822418016907809440*c +
    916989071310980190360
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    69797956124766506054850*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    155441833382999023953300*a*b +
    12538510013147704914564*a*c +
    750158661135580269086520*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    572291440410105944510472*b +
    46728001487548069835688*c +
    1791991105505428147714872
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    84039658576214850*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    168079317152429700*a*b +
    19594833139302084*a*c +
    972422966099796120*a +
    4939531327620558*b^2 +
    9879062655241116*b*c +
    660028338973728072*b +
    66090402921217608*c +
    2570156628314641272
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12551089801883255576964*a +
    4131316686778000053516*b +
    46761599545281365992488
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    69846316899425807645250*a^2 +
    223430341148344939680*a*b^2 +
    155494580384419175639700*a*b +
    750555793253731792315320*a +
    2070780247772652157758*b^2 +
    572462122767428813184072*b +
    1792857754412146442041272
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50164*graphDir cfg scale f 0 b c = scale*131073*80910*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50164*graphDir cfg scale f (a+1) b c = scale*131073*80910*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50164*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c+fullSlack a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50164
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50164) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50164)*50164 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G15
end MergedPart3
