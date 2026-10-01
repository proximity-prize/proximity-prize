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
    267221415066983440*b +
    2213109137705872420
def helperSlackLo0 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204678651603008*b +
    100761785620725304728*c +
    2488187413034073798840
def gLo1 (b c : ℕ) : ℕ :=
    5325894189560*b +
    5325894189560*c +
    416623600372320
def identitySlackLo1 (b c : ℕ) : ℕ :=
    267221415066983440*b +
    267221415066983440*c +
    20653495452667885680
def helperSlackLo1 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204678651603008*b +
    100761785620725304728*c +
    2488187413034073798840
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    181217906410296*b +
    18099455723173*c +
    640142708903136
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10343950911012864*b^2 +
    20687901822025728*b*c +
    8992356407265032304*b +
    858086676971902502*c +
    31718236578908303664
def helperSlackLo2 (b c : ℕ) : ℕ :=
    5366968872448819320*b^2 +
    10735540832850842736*b*c +
    877120204678651603008*b +
    100761785620725304728*c +
    2488187413034073798840
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
    10343950911012864*a^2 +
    20687901822025728*a*b +
    894290505160447526*a +
    282737341433502736*b +
    3091883637582922314
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724445787344848*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923902365954688*a*b +
    35946531869381896356*a*c +
    1727020461260833677072*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470116445772120*b +
    135872055937582211412*c +
    4049981544985553420784
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    181630229562168*a +
    5635136553464*b +
    5635136553464*c +
    597944585997720
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10343950911012864*a^2 +
    20687901822025728*a*b +
    20687901822025728*a*c +
    9013044309087058032*a +
    282737341433502736*b +
    282737341433502736*c +
    29651023756471546080
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724445787344848*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923902365954688*a*b +
    35946531869381896356*a*c +
    1727020461260833677072*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470116445772120*b +
    135872055937582211412*c +
    4049981544985553420784
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
    10343950911012864*a^2 +
    20687901822025728*a*b +
    20687901822025728*a*c +
    9013044309087058032*a +
    10343950911012864*b^2 +
    20687901822025728*b*c +
    9013044309087058032*b +
    878774578793928230*c +
    40720936937084348832
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184589093839141368*a^3 +
    555370369470628200*a^2*b +
    556973457423832296*a^2*c +
    165224724445787344848*a^2 +
    556973457423832296*a*b^2 +
    1115550002800868688*a*b*c +
    330374923902365954688*a*b +
    35946531869381896356*a*c +
    1727020461260833677072*a +
    5830846771673535840*b^2 +
    11664899719253479872*b*c +
    1206660470116445772120*b +
    135872055937582211412*c +
    4049981544985553420784
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
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    280151472082271200*b +
    2220276415199600460
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791163017154244*b +
    119313871648306985418*c +
    4763039898301068044994
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    680900360593670
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280151472082271200*b +
    280151472082271200*c +
    33871621441278417580
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791163017154244*b +
    119313871648306985418*c +
    4763039898301068044994
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    297502834388595*b +
    18297029134004*c +
    1052034857286092
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12067942729515008*b^2 +
    24135885459030016*b*c +
    14810157912154013130*b +
    859660489539840496*c +
    52317799282275131008
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1670129791163017154244*b +
    119313871648306985418*c +
    4763039898301068044994
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    901898289093143024*a +
    298253386176543712*b +
    3104072698128779580
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035926128909042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239231190744520*a*b +
    42985986833672287212*a*c +
    3307868994557532978000*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149937311634384*b +
    161161705128390097350*c +
    7755243581411811964152
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    297983878065779*a +
    5944381276688*b +
    5944381276688*c +
    978523454066553
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    14834293797613043146*a +
    298253386176543712*b +
    298253386176543712*c +
    48687813232727496822
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035926128909042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239231190744520*a*b +
    42985986833672287212*a*c +
    3307868994557532978000*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149937311634384*b +
    161161705128390097350*c +
    7755243581411811964152
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    14834293797613043146*a +
    12067942729515008*b^2 +
    24135885459030016*b*c +
    14834293797613043146*b +
    883796374998870512*c +
    67140025137158659146
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    315663035926128909042*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    631151239231190744520*a*b +
    42985986833672287212*a*c +
    3307868994557532978000*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2300145149937311634384*b +
    161161705128390097350*c +
    7755243581411811964152
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
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    280151472082271200*b +
    2274151850054993560
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778487425844798*b +
    121939515288971022438*c +
    4318407598433593182774
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    617762568719450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280151472082271200*b +
    280151472082271200*c +
    30703745871781303300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778487425844798*b +
    121939515288971022438*c +
    4318407598433593182774
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    269722273014813*b +
    18769487660769*c +
    953539468824692
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12067942729515008*b^2 +
    24135885459030016*b*c +
    13416296025785875062*b +
    883365623661747606*c +
    47375891661612847408
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6641187994447826898*b^2 +
    13284664038233184102*b*c +
    1515742778487425844798*b +
    121939515288971022438*c +
    4318407598433593182774
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    925603423215050134*a +
    298253386176543712*b +
    3181653267106079790
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393752265623010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471340644205792*a*b +
    43981906407540296172*a*c +
    2999020156401692722608*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369371173786210*b +
    164783268342922143330*c +
    7031051085562360132572
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    270203316691997*a +
    5944381276688*b +
    5944381276688*c +
    887605100818551
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    13440431911244905078*a +
    298253386176543712*b +
    298253386176543712*c +
    44126075776862244474
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393752265623010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471340644205792*a*b +
    43981906407540296172*a*c +
    2999020156401692722608*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369371173786210*b +
    164783268342922143330*c +
    7031051085562360132572
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    13440431911244905078*a +
    12067942729515008*b^2 +
    24135885459030016*b*c +
    13440431911244905078*b +
    907501509120777622*c +
    60804255630128237478
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251155143586703832*a^3 +
    755738327453022396*a^2*b +
    758011224145933296*a^2*c +
    286374393752265623010*a^2 +
    758011224145933296*a*b^2 +
    1518295344984777492*a*b*c +
    572591471340644205792*a*b +
    43981906407540296172*a*c +
    2999020156401692722608*a +
    7272485819933852610*b^2 +
    14549532585898146426*b*c +
    2087198369371173786210*b +
    164783268342922143330*c +
    7031051085562360132572
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
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    229293200471932064*b +
    1927784243358056540
def helperSlackLo0 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792780765035432*b +
    88626013219367489952*c +
    4063930875145242360414
def gLo1 (b c : ℕ) : ℕ :=
    4569960546736*b +
    4569960546736*c +
    677017586556770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    229293200471932064*b +
    229293200471932064*c +
    33718503315486479980
def helperSlackLo1 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792780765035432*b +
    88626013219367489952*c +
    4063930875145242360414
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    296214311824897*b +
    16020638205407*c +
    1047860014200836
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10343950911012864*b^2 +
    20687901822025728*b*c +
    14762186052537222878*b +
    753784086835511218*c +
    52175044654915103464
def helperSlackLo2 (b c : ℕ) : ℕ :=
    4684405022671474368*b^2 +
    9370268410078155240*b*c +
    1422643792780765035432*b +
    88626013219367489952*c +
    4063930875145242360414
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
    10343950911012864*a^2 +
    20687901822025728*a*b +
    789987915024056242*a +
    244809126838451360*b +
    2702256153098715150
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603768539730338*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190001246972788*a*b +
    32192135683147694556*a*c +
    2822771716205231639988*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923545451921620*b +
    119981686963996044324*c +
    6617563583104361710296
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    296626634976769*a +
    4879202910640*b +
    4879202910640*c +
    973334977596771
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10343950911012864*a^2 +
    20687901822025728*a*b +
    20687901822025728*a*c +
    14782873954359248606*a +
    244809126838451360*b +
    244809126838451360*c +
    48485861264562330954
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603768539730338*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190001246972788*a*b +
    32192135683147694556*a*c +
    2822771716205231639988*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923545451921620*b +
    119981686963996044324*c +
    6617563583104361710296
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
    10343950911012864*a^2 +
    20687901822025728*a*b +
    20687901822025728*a*c +
    14782873954359248606*a +
    10343950911012864*b^2 +
    20687901822025728*b*c +
    14782873954359248606*b +
    774471988657536946*c +
    66947574658363339206
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184789479833291880*a^3 +
    555771141458929224*a^2*b +
    557173843417982808*a^2*c +
    269137603768539730338*a^2 +
    557173843417982808*a*b^2 +
    1115750388795019200*a*b*c +
    538145190001246972788*a*b +
    32192135683147694556*a*c +
    2822771716205231639988*a +
    5148483307890341400*b^2 +
    10299827682474942888*b*c +
    1959953923545451921620*b +
    119981686963996044324*c +
    6617563583104361710296
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
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    2765741486136329034*b +
    22332606678363735700
def helperSlackLo0 (b c : ℕ) : ℕ :=
    677767242150697505598*b^2 +
    1340242490172386980044*b*c +
    158047503409715647252500*b +
    12455799148799497205316*c +
    439483069397991397207842
def gLo1 (b c : ℕ) : ℕ :=
    55123001676891*b +
    53705626096596*c +
    5991631187983990
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2765741486136329034*b +
    2694626083770607704*c +
    297621978356953938260
def helperSlackLo1 (b c : ℕ) : ℕ :=
    677517160429997666622*b^2 +
    1339992408451687141068*b*c +
    158046543396881855491860*b +
    12454090256686691809476*c +
    439484491836745490358306
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2825190268278957*b +
    188845957072176*c +
    9513062221596442
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124127410932154368*b^2 +
    248254821864308736*b*c +
    140550246573046478118*b +
    8874732076348403424*c +
    472504979535208176908
def helperSlackLo2 (b c : ℕ) : ℕ :=
    677364867074443277502*b^2 +
    1339840115096132751948*b*c +
    158043823541783258891220*b +
    12453275887792427162628*c +
    439474696483819652325666
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
    124127410932154368*a^2 +
    248254821864308736*a*b +
    9119536941635686832*a +
    2951932602534560586*b +
    31265951556598650948
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26609655264958841184*a^3 +
    80030954876980239648*a^2*b +
    80232943959083955744*a^2*c +
    28586967199596657013122*a^2 +
    80232943959083955744*a*b^2 +
    160667877000271627584*a*b*c +
    59419456764360845417748*a*b +
    4521512652159015000900*a*c +
    302126749290588999591864*a +
    744594425729108789598*b^2 +
    1474098846411313264140*b*c +
    217346711733504945768456*b +
    16856861371304861588328*c +
    713022649214382255990456
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2621028002155232*a +
    58833910043739*b +
    57416534463444*c +
    8608948262898006
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    130306609032554699968*a +
    2951932602534560586*b +
    2880817200168839256*c +
    427742395326107866644
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26532707043205044576*a^3 +
    79877058433472646432*a^2*b +
    80155995737330159136*a^2*c +
    28586278047672549126018*a^2 +
    80155995737330159136*a*b^2 +
    160590928778517830976*a*b*c +
    59418440582494283895060*a*b +
    4520557211641059889476*a*c +
    302125514549727217063608*a +
    744267395786655154014*b^2 +
    1473771816468859628556*b*c +
    217344889435248100078344*b +
    16854273986895854877672*c +
    713023449115976920703160
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
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    130306609032554699968*a +
    124127410932154368*b^2 +
    248254821864308736*b*c +
    140798501394910786854*b +
    9122986898212712160*c +
    602687461156830722508
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26484614404608921696*a^3 +
    79780873156280400672*a^2*b +
    80107903098734036256*a^2*c +
    28585065822342794699778*a^2 +
    80107903098734036256*a*b^2 +
    160542836139921708096*a*b*c +
    59417027971170378956820*a*b +
    4520049032698740772164*a*c +
    302117137430450506456248*a +
    744067009792504642014*b^2 +
    1473571430474709116556*b*c +
    217340853154102790785224*b +
    16852999531697867236392*c +
    713006440776465530366520
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
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4872049531803150408*b +
    40631304190792867040
def helperSlackLo0 (b c : ℕ) : ℕ :=
    2087719876592441417178*b^2 +
    4191819108741119496744*b*c +
    468472780583227365146460*b +
    38768615579087371444788*c +
    1224863415895962505021614
def gLo1 (b c : ℕ) : ℕ :=
    97103071945692*b +
    97953497293869*c +
    9055043078043960
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4872049531803150408*b +
    4914718773222583206*c +
    449074012877106791040
def helperSlackLo1 (b c : ℕ) : ℕ :=
    2087263297104769475586*b^2 +
    4191362529253447555152*b*c +
    468471084283215855312408*b +
    38765414612580051192012*c +
    1224866289731444224407126
def gLo2 (b c : ℕ) : ℕ :=
    4329393094656*b^2 +
    8658786189312*b*c +
    5147547234039522*b +
    328496099063895*c +
    15475693921132356
def identitySlackLo2 (b c : ℕ) : ℕ :=
    217222969131270144*b^2 +
    434445938262540288*b*c +
    256171547512430633628*b +
    15431219570297696130*c +
    768071509149344347944
def helperSlackLo2 (b c : ℕ) : ℕ :=
    2086330500301998842226*b^2 +
    4190429732450676921792*b*c +
    468462417766499638455120*b +
    38759859560835732818736*c +
    1224846219651660217722582
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
    217222969131270144*a^2 +
    434445938262540288*a*b +
    16622933403275851036*a +
    5197883985500055624*b +
    56928401483117367804
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    81492086028893745240*a^3 +
    245094849650623866264*a^2*b +
    245713441214566496808*a^2*c +
    75597267763534079983374*a^2 +
    245713441214566496808*a*b^2 +
    492045473993075624160*a*b*c +
    173880581836034611999908*a*b +
    14060237442358442282424*a*c +
    819358611167060864082576*a +
    2292378176641197856770*b^2 +
    4601754300402575006472*b*c +
    641985101519671742877288*b +
    52459973530291636827588*c +
    1968624139850302202289288
def gHi1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3957106279299264*a +
    103597161587676*b +
    104447586935853*c +
    13005655234671096
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    217222969131270144*a^2 +
    434445938262540288*a*b +
    434445938262540288*a*c +
    196442363049292928736*a +
    5197883985500055624*b +
    5240553226919488422*c +
    645190539815448369504
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    81344802323193118920*a^3 +
    244800282239222613624*a^2*b +
    245566157508865870488*a^2*c +
    75595941319494057199398*a^2 +
    245566157508865870488*a*b^2 +
    491898190287374997840*a*b*c +
    173878651528801216648020*a*b +
    14058416033677328858280*a*c +
    819356226138335171405736*a +
    2291774313447825288858*b^2 +
    4601150437209202438560*b*c +
    641981769479838238943988*b +
    52455098438808903776988*c +
    1968625807817392551155616
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
    217222969131270144*a^2 +
    434445938262540288*a*b +
    434445938262540288*a*c +
    196442363049292928736*a +
    217222969131270144*b^2 +
    434445938262540288*b*c +
    256605993450693173916*b +
    15865665508560236418*c +
    964296649229506006536
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    81050234911791866280*a^3 +
    244211147416420108344*a^2*b +
    245271590097464617848*a^2*c +
    75591422837808470364726*a^2 +
    245271590097464617848*a*b^2 +
    491603622875973745200*a*b*c +
    173872905682901457927348*a*b +
    14055097240467643387896*a*c +
    819333241493766557658696*a +
    2290546949233653402858*b^2 +
    4599923072995030552560*b*c +
    641967946252045065871308*b +
    52446519161266301185968*c +
    1968586977007314116306064
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
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    358162881181042362*b +
    2850515754565184740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
def gLo1 (b c : ℕ) : ℕ :=
    7138415936163*b +
    7138415936163*c +
    740894169953600
def identitySlackLo1 (b c : ℕ) : ℕ :=
    358162881181042362*b +
    358162881181042362*c +
    36798358474632579400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
def gLo2 (b c : ℕ) : ℕ :=
    309242363904*b^2 +
    618484727808*b*c +
    323324839032829*b +
    23511252928669*c +
    1142799052169204
def identitySlackLo2 (b c : ℕ) : ℕ :=
    15515926366519296*b^2 +
    31031852733038592*b*c +
    16072394230185423446*b +
    1104600482719169006*c +
    56738374097141178496
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
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
    15515926366519296*a^2 +
    31031852733038592*a*b +
    1158906225001986542*a +
    381436770730821306*b +
    3986147971642074834
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
def gHi1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    323943323760637*a +
    7602279482019*b +
    7602279482019*c +
    1064373627809085
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    15515926366519296*a^2 +
    31031852733038592*a*b +
    31031852733038592*a*c +
    16103426082918462038*a +
    381436770730821306*b +
    381436770730821306*c +
    52878510549625944990
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
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
    15515926366519296*a^2 +
    31031852733038592*a*b +
    31031852733038592*a*c +
    16103426082918462038*a +
    15515926366519296*b^2 +
    31031852733038592*b*c +
    16103426082918462038*b +
    1135632335452207598*c +
    72826284253693121238
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
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
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    11395699956266104880*b +
    92608200213360394200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10788159601498425061506*b^2 +
    21513302885187504249732*b*c +
    2123003999485637569676556*b +
    196405984272909192954288*c +
    5775658061067928159053366
def gLo1 (b c : ℕ) : ℕ :=
    227123608966120*b +
    225611741680472*c +
    19948839528421450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11395699956266104880*b +
    11319843527076002128*c +
    989238144453082592300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10784377501401421323906*b^2 +
    21509520785090500512132*b*c +
    2122970546028311346274956*b +
    196380006573609546997488*c +
    5775584890903728231942966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9983821590984960*b +
    748511705502288*c +
    32350456257847930
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    496258292487705287040*b +
    35220840302684750112*c +
    1604471886393372079820
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10782074299419271611906*b^2 +
    21507217583108350800132*b*c +
    2122948347161968733348556*b +
    196366357068099407264688*c +
    5775531339147457547315766
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    37640470415771590220*a +
    12119776520037005360*b +
    129524590382573428260
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369802462594925355080742*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    793823106269087012118684*a*b +
    70803773427188919899448*a*c +
    3935504907308918744447544*a +
    11799109461508455794466*b^2 +
    23537966447586145370052*b*c +
    2915007950892128091407880*b +
    265387838995123042811976*c +
    9341357737923496157128488
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    241554919281640*b +
    240043051995992*c +
    28645297412075655
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    12119776520037005360*b +
    12043920090846902608*c +
    1420904250289174577970
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785154873864220923942*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    793800852724822103843484*a*b +
    70789275375337310497848*a*c +
    3935419098604909425829944*a +
    11794163638304681676066*b^2 +
    23533020624382371251652*b*c +
    2914954571336750500492680*b +
    265348526967078557834376*c +
    9341214903053241275176488
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    497223727906066487680*b +
    36186275721045950752*c +
    2036379354766842021330
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369773707198184844786342*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    793786374520218846505884*a*b +
    70781105068433675694648*a*c +
    3935359511252512594885944*a +
    11791133109380800476066*b^2 +
    23529990095458490051652*b*c +
    2914919348919688093204680*b +
    265327434481606514786376*c +
    9341112484293311404254888
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
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    11206058883290848000*b +
    92366835308439963000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10628812564384132664706*b^2 +
    21353955800720917334532*b*c +
    2162637281768824290078156*b +
    196203663257892546483888*c +
    5826402928650630267414966
def gLo1 (b c : ℕ) : ℕ :=
    223343940752000*b +
    225611741680472*c +
    19944028971062650
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11206058883290848000*b +
    11319843527076002128*c +
    988996779548162161100
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10625078952749911026306*b^2 +
    21350222189086695696132*b*c +
    2162592448509129388066956*b +
    196177261284636042267888*c +
    5826271604277057136326966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    10301313720971040*b +
    748511705502288*c +
    32754543075987130
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    512188142617626864960*b +
    35220840302684750112*c +
    1624746538406688300620
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10622727262304979215106*b^2 +
    21347870498641763884932*b*c +
    2162581629445155453750156*b +
    196164036053082760794288*c +
    5826276206730159655677366
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    37640470415771590220*a +
    11930135447061748480*b +
    129283225477652997060
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369806733557242919355942*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    807208406829668659293084*a*b +
    70803967854562993480248*a*c +
    3952577168197627026162744*a +
    11639762424394163397666*b^2 +
    23378619363119558454852*b*c +
    2968026533735896458983880*b +
    265185712407480469922376*c +
    9409170595432588982930088
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    237775251067520*b +
    240043051995992*c +
    28640486854716855
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    11930135447061748480*b +
    12043920090846902608*c +
    1420662885384254146770
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785158851456960469542*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    807181934789141708387484*a*b +
    70789275848860255681848*a*c +
    3952449854027207925849144*a +
    11634865089653171378466*b^2 +
    23373722028378566435652*b*c +
    2967957555881888146828680*b +
    265145782151627998288776*c +
    9408932367871275940034088
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    513153578035988065600*b +
    36186275721045950752*c +
    2056654006780158242130
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369777978160502409061542*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    807171675080800493680284*a*b +
    70781299495807749275448*a*c +
    3952431772141220876601144*a +
    11631786072266508079266*b^2 +
    23370643010991903136452*b*c +
    2967937931763456460780680*b +
    265125307893963941896776*c +
    9408925341802404230056488
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
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    11585341029241361760*b +
    94358077294231832200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10947603688046482638006*b^2 +
    21672747091596057325932*b*c +
    2012795416473151058045340*b +
    198547667234261671078512*c +
    5521658595317978282234310
def gLo1 (b c : ℕ) : ℕ :=
    230903277180240*b +
    225611741680472*c +
    19232075321503450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11585341029241361760*b +
    11319843527076002128*c +
    953275217135178860300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10943409436015831057206*b^2 +
    21668552839565405745132*b*c +
    2012762624668687268966940*b +
    198518428685285018297712*c +
    5521598959896139992650310
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9348837331012800*b +
    753803241002056*c +
    30820707857292730
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    464398592227862131200*b +
    35486337804850109744*c +
    1527718290143915475020
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10941057745570899246006*b^2 +
    21666201149120473933932*b*c +
    2012731270740725115638940*b +
    198505470140277038369712*c +
    5521500905171079990439110
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    38304214171184989300*a +
    12309417593012262240*b +
    131938211218858265340
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    356409437379866047279206*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    753668055357067013763612*a*b +
    71585210393289432845256*a*c +
    3777248171616654000979512*a +
    11958553548056513370966*b^2 +
    23697410653994698446252*b*c +
    2764644316967621581421592*b +
    268310958922576033882008*c +
    8942494561696340844642936
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8393397137383965*a +
    245334587495760*b +
    240043051995992*c +
    27611041075171575
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    416460335952728963910*a +
    12309417593012262240*b +
    12043920090846902608*c +
    1369011472841349268050
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401412015874457841120*a^3 +
    1208309078497069856160*a^2*b +
    1212382109370766188960*a^2*c +
    356391566312944080626406*a^2 +
    1212382109370766188960*a*b^2 +
    2428837249615228710720*a*b*c +
    753644680849619278851612*a*b +
    71568845535435742406856*a*c +
    3777167371142417842502712*a +
    11953050107530745111766*b^2 +
    23691907213468930187052*b*c +
    2764590769032700290787992*b +
    268266664704240807341208*c +
    8942370687678693246556536
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
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    416460335952728963910*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    465364027646223331840*b +
    36451773223211310384*c +
    1943695908387463838610
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400684688932726353120*a^3 +
    1206854424613606880160*a^2*b +
    1211654782429034700960*a^2*c +
    356376918398721085941606*a^2 +
    1211654782429034700960*a*b^2 +
    2428109922673497222720*a*b*c +
    753626953918009620867612*a*b +
    71560966159308800198856*a*c +
    3777076489543489662470712*a +
    11949971090144081812566*b^2 +
    23688828196082266887852*b*c +
    2764543142827011942451992*b +
    268246554110047616693208*c +
    8942195671941986327510136
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
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    2893749210394627428*b +
    23443735642639945320
def helperSlackLo0 (b c : ℕ) : ℕ :=
    705412122723948431916*b^2 +
    1392464875200549283512*b*c +
    137060163644446227076884*b +
    12745137084326426595312*c +
    378066895713808981002630
def gLo1 (b c : ℕ) : ℕ :=
    57674277721422*b +
    55973427025068*c +
    5137578772834220
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2893749210394627428*b +
    2808410727555761832*c +
    254770752479229378280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    705134788508044123308*b^2 +
    1392187540984644974904*b*c +
    137058524389053178783380*b +
    12743203759863480574704*c +
    378065597569894650561030
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2462909069955555*b +
    188845957072176*c +
    8194670757388502
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124127410932154368*b^2 +
    248254821864308736*b*c +
    122373149728368106170*b +
    8874732076348403424*c +
    406356006210038995348
def helperSlackLo2 (b c : ℕ) : ℕ :=
    704982495152489734188*b^2 +
    1392035247629090585784*b*c +
    137056448173767793627284*b +
    12742389390969215927856*c +
    378059020417374129624582
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
    124127410932154368*a^2 +
    248254821864308736*a*b +
    9536747302181251968*a +
    3079940326792858980*b +
    32794290881420425704
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26600036737239616608*a^3 +
    80011717821541790496*a^2*b +
    80223325431364731168*a^2*c +
    24495889584749406296382*a^2 +
    80223325431364731168*a*b^2 +
    160658258472552403008*a*b*c +
    51402107863738154696940*a*b +
    4611631787521216786656*a*c +
    259193458038404538956232*a +
    772229687774640491340*b^2 +
    1526311612911756343032*b*c +
    188342042304668273321184*b +
    17236328060721711988656*c +
    612764252274334910641776
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2243817114386056*a +
    61385186088270*b +
    59684335391916*c +
    7377684959979060
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    111380429949624063344*a +
    3079940326792858980*b +
    2994601843953993384*c +
    365964990365452670040
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26513469987766595424*a^3 +
    79838584322595748128*a^2*b +
    80136758681891709984*a^2*c +
    24494900276593032176574*a^2 +
    80136758681891709984*a*b^2 +
    160571691723079381824*a*b*c +
    51400754654616403247340*a*b +
    4610549703042727867872*a*c +
    259189990926441501048264*a +
    771865786809263161548*b^2 +
    1525947711946379013240*b*c +
    188339222973652419620448*b +
    17233399218529750070448*c +
    612760389759864443390832
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
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    111380429949624063344*a +
    124127410932154368*b^2 +
    248254821864308736*b*c +
    122621404550232414906*b +
    9122986898212712160*c +
    517612308748730904324
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26465377349170472544*a^3 +
    79742399045403502368*a^2*b +
    80088666043295587104*a^2*c +
    24493922102104445548350*a^2 +
    80088666043295587104*a*b^2 +
    160523599084483258944*a*b*c +
    51399576094133666107116*a*b +
    4610041524100408750560*a*c +
    259183895803312596429384*a +
    771665400815112649548*b^2 +
    1525747325952228501240*b*c +
    188336064383161489569888*b +
    17232124763331762429168*c +
    612748647566065008340848
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
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4609569143560548390*b +
    37853149566242838540
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882708954581030949278*b^2 +
    3757053275717680215756*b*c +
    418730590437659977232340*b +
    34486527131241078222468*c +
    1119334564007250804763650
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8862743329077330
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4585864009438641280*c +
    439675742344867995420
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    418729737045366190856340*b +
    34482036257577733475268*c +
    1119345681353080905029250
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14731795051764750
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14411937981296825280*c +
    731147410975291726500
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    418718765823297607539540*b +
    34477046645134291470468*c +
    1119311928169290574142850
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15477368476423188144*a +
    4919887670890934310*b +
    53020197936998074044
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73888981466606811360*a^3 +
    222254743315995269280*a^2*b +
    222842542232170104480*a^2*c +
    70480173771798725379618*a^2 +
    222842542232170104480*a*b^2 +
    446272883380515044160*a*b*c +
    156125970423189310679316*a*b +
    12523457003250956983812*a*c +
    756455296475903196806136*a +
    2068313273533554743358*b^2 +
    4128849712538902639116*b*c +
    574522590879492829691976*b +
    46675426354219402151400*c +
    1805309098109859542342328
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3874125390125628*a +
    98056516739565*b +
    97584058212800*c +
    12730683840467598
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    192378950744860075272*a +
    4919887670890934310*b +
    4896182536769027200*c +
    631744372984060118052
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    70479066510077722938018*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    156124057164469613956116*a*b +
    12521021199928686353412*a*c +
    756457799278324576367736*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    574520198282335094215176*b +
    46668686704161660585000*c +
    1805323638492904150799928
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    192378950744860075272*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    14825696017737339840*c +
    923319482701931544492
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    70473837046379595526818*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    156117714445248428144916*a*b +
    12518028768742964158212*a*c +
    756425924668892844479736*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    574503418703696393119176*b +
    46660971841858030401000*c +
    1805262972982054681420728
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
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4609569143560548390*b +
    38111751653548725420
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882851443711615301534*b^2 +
    3723060364136351206668*b*c +
    415192427700408356478228*b +
    34921690602697051626564*c +
    1101640197860846139721698
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    89509376827660*c +
    8666887321630770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4491043472951012840*c +
    429848863027244293980
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089976933843355934*b^2 +
    3722298897358579261068*b*c +
    415188747531625823819028*b +
    34916634195041135543364*c +
    1101640753208015400534498
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    314743261786960*c +
    14535939044318190
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14791220127247339040*c +
    721320531657668025060
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881168201360751000734*b^2 +
    3721377121785486905868*b*c +
    415178877502494305545428*b +
    34911241583996424032964*c +
    1101614396949003661926498
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15591153120208342272*a +
    4919887670890934310*b +
    53392584668089115052
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73942417731713614560*a^3 +
    222361615846208875680*a^2*b +
    222895978497276907680*a^2*c +
    68923743352521493880322*a^2 +
    222895978497276907680*a*b^2 +
    446326319645621847360*a*b*c +
    154569734843519657028564*a*b +
    12701477709937859827716*a*c +
    742019111683121563822584*a +
    2068509198929245898814*b^2 +
    4094910237222680433228*b*c +
    569428085690041341680712*b +
    47288557096097171596200*c +
    1774735031026215582619320
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    98056516739565*b +
    95694224105740*c +
    12448651397739102
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    188055134281024218408*a +
    4919887670890934310*b +
    4801362000281398760*c +
    617593677202600559748
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    68921289173767430965122*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    154566278734794841553364*a*b +
    12698578792250048659716*a*c +
    742012372688126825393784*a +
    2067507268958493338814*b^2 +
    4093908307251927873228*b*c +
    569421430338919954775112*b +
    47280842233946424959400*c +
    1774731061093951187304120
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    188055134281024218408*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    15204978163687853600*c +
    909168786920471986188
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73408055080645582560*a^3 +
    221292890544072811680*a^2*b +
    222361615846208875680*a^2*c +
    68916312480147957905922*a^2 +
    222361615846208875680*a*b^2 +
    445791956994553815360*a*b*c +
    154560086366144188721364*a*b +
    12695314726682726093316*a*c +
    741984895523995064398584*a +
    2066291593927313566014*b^2 +
    4092692632220748100428*b*c +
    569405955740053958504712*b +
    47272479456792478300200*c +
    1774681910464969073342520
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
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4609569143560548390*b +
    38111751653548725420
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882784660218305427134*b^2 +
    3757128985616661200268*b*c +
    415191809059404435999828*b +
    34580026949459771111364*c +
    1101638771559723681978498
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8666887321630770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4585864009438641280*c +
    429848863027244293980
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882098894816101452734*b^2 +
    3756443220214457225868*b*c +
    415189746267672146910228*b +
    34575226590676080824964*c +
    1101645513368693692343298
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14535939044318190
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14411937981296825280*c +
    721320531657668025060
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881177119243009097534*b^2 +
    3755521444641364870668*b*c +
    415179876238540628636628*b +
    34569833979631369314564*c +
    1101619157109681953735298
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15591153120208342272*a +
    4919887670890934310*b +
    53392584668089115052
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73915699599160212960*a^3 +
    222308179581102072480*a^2*b +
    222869260364723506080*a^2*c +
    68923346466735700940322*a^2 +
    222869260364723506080*a*b^2 +
    446299601513068445760*a*b*c +
    154569244929630945996564*a*b +
    12564691126442038867716*a*c +
    742017197691350794702584*a +
    2068415697303382622814*b^2 +
    4128952140570437025228*b*c +
    569427030571413816973512*b +
    46810133577496623522600*c +
    1774732060900975595294520
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3787948954843692*a +
    98056516739565*b +
    97584058212800*c +
    12448651397739102
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    188055134281024218408*a +
    4919887670890934310*b +
    4896182536769027200*c +
    617593677202600559748
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    68921628088807459532322*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    154566627041240073401364*a*b +
    12562010406870721267716*a*c +
    742015696662922324596984*a +
    2067516186840751435614*b^2 +
    4128052630107805838028*b*c +
    569422777381411509714312*b +
    46802866244202042849000*c +
    1774738806314384949748920
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    188055134281024218408*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    14825696017737339840*c +
    909168786920471986188
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73408055080645582560*a^3 +
    221292890544072811680*a^2*b +
    222361615846208875680*a^2*c +
    68916651395187986473122*a^2 +
    222361615846208875680*a*b^2 +
    445791956994553815360*a*b*c +
    154560434672589420569364*a*b +
    12558746341303398701316*a*c +
    741988219498790563601784*a +
    2066300511809571662814*b^2 +
    4126836955076626065228*b*c +
    569407302782545513443912*b +
    46794503467048096189800*c +
    1774689655685402835787320
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
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4609569143560548390*b +
    37982450609895781980
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882775749912414453278*b^2 +
    3757120071049063719756*b*c +
    417194329359196612949652*b +
    34533409509268229724804*c +
    1111651592552667452019042
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8777700589001850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4585864009438641280*c +
    435408807904320861900
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    417192266567464323860052*b +
    34528609150484539438404*c +
    1111658334361637462383842
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14646752311689270
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14411937981296825280*c +
    726880476534744592980
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    417182079077283973656852*b +
    34523595046419590148804*c +
    1111628498260750072822242
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15534260798315765208*a +
    4919887670890934310*b +
    53206391302543594548
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73915699599160212960*a^3 +
    222308179581102072480*a^2*b +
    222869260364723506080*a^2*c +
    69804404940697736832450*a^2 +
    222869260364723506080*a*b^2 +
    446299601513068445760*a*b*c +
    155450294680802177207700*a*b +
    12544192069948929176964*a*c +
    750187171147548720667320*a +
    2068406786997491648958*b^2 +
    4128943226002839544716*b*c +
    572310600622377225134472*b +
    46743017080811972445288*c +
    1792033796876155255407672
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    98056516739565*b +
    97584058212800*c +
    12608222385072330
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    190501504122405032160*a +
    4919887670890934310*b +
    4896182536769027200*c +
    625599991921057941420
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    69802686562769495424450*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    155447676792411304612500*a*b +
    12541511350377611576964*a*c +
    750185670119120250561720*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    572306347432374917875272*b +
    46735749747517391771688*c +
    1792040542289564609862072
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    190501504122405032160*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    14825696017737339840*c +
    917175101638929367860
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    69797742092485270963650*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    155441619066604021751700*a*b +
    12538510013147704914564*a*c +
    750156573669961331025720*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    572290636579038352843272*b +
    46728001487548069835688*c +
    1791986287028476991209272
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
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    4609569143560548390*b +
    37982450609895781980
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882708954581030949278*b^2 +
    3757053275717680215756*b*c +
    417193709463356887733652*b +
    34533100024147884185604*c +
    1111650161978000413990242
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8777700589001850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4585864009438641280*c +
    435408807904320861900
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    417192856071063101357652*b +
    34528609150484539438404*c +
    1111661279323830514255842
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14646752311689270
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14411937981296825280*c +
    726880476534744592980
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    417182668580882751154452*b +
    34523595046419590148804*c +
    1111631443222943124694242
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15534260798315765208*a +
    4919887670890934310*b +
    53206391302543594548
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73888981466606811360*a^3 +
    222254743315995269280*a^2*b +
    222842542232170104480*a^2*c +
    69804007853664692189250*a^2 +
    222842542232170104480*a*b^2 +
    446272883380515044160*a*b*c +
    155449804364418962769300*a*b +
    12543947153699882207364*a*c +
    750185254740810931108920*a +
    2068313273533554743358*b^2 +
    4128849712538902639116*b*c +
    572309543846419392283272*b +
    46742489397575133338088*c +
    1792030820263650919062072
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3836706674805840*a +
    98056516739565*b +
    97584058212800*c +
    12608222385072330
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    190501504122405032160*a +
    4919887670890934310*b +
    4896182536769027200*c +
    625599991921057941420
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    69802900591943689747650*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    155447891105699266046100*a*b +
    12541511350377611576964*a*c +
    750187757543232310670520*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    572307151249261656806472*b +
    46735749747517391771688*c +
    1792045360646695527519672
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
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    190501504122405032160*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    14825696017737339840*c +
    917175101638929367860
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    69797956121659465286850*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    155441833379891983185300*a*b +
    12538510013147704914564*a*c +
    750158661094073391134520*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    572291440395925091774472*b +
    46728001487548069835688*c +
    1791991105385607908866872
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
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G15
end MergedPart3
