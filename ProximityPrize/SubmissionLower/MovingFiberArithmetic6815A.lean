import ProximityPrize.SubmissionLower.HFreeDirArith6815
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
