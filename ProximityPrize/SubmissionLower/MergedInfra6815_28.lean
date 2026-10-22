import ProximityPrize.SubmissionLower.MergedInfra6815_27
import ProximityPrize.SubmissionLower.MergedInfra6815_22
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G16
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source27,source27,source27]
def scale : ℕ := 9
def denominator : ℕ := 4064094
def gLo0 (b c : ℕ) : ℕ :=
    3135405621545*b +
    25727621663120
def identitySlackLo0 (b c : ℕ) : ℕ :=
    157284487599183380*b +
    1228048413946429130
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099997820258222*b +
    27799225870370845752*c +
    661960166450974131798
def gLo1 (b c : ℕ) : ℕ :=
    3135405621545*b +
    3135405621545*c +
    222013137897940
def identitySlackLo1 (b c : ℕ) : ℕ :=
    157284487599183380*b +
    157284487599183380*c +
    11011963051187617060
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099997820258222*b +
    27799225870370845752*c +
    661960166450974131798
def gLo2 (b c : ℕ) : ℕ :=
    103080787968*b^2 +
    206161575936*b*c +
    96372947231681*b +
    9852907357087*c +
    340507472465668
def identitySlackLo2 (b c : ℕ) : ℕ :=
    5170944647626752*b^2 +
    10341889295253504*b*c +
    4784410925600187644*b +
    469240444995983248*c +
    16881050260556241652
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099997820258222*b +
    27799225870370845752*c +
    661960166450974131798
def fullSlackLo (b c : ℕ) : ℕ :=
    310018318690410*b^2 +
    620036637380820*b*c +
    46566253490589450*b +
    5540143947972390*c +
    131899415922487080
def fullSlackHi (a b c : ℕ) : ℕ :=
    9277270917120*a^3 +
    27831812751360*a^2*b +
    27831812751360*a^2*c +
    8747783418188250*a^2 +
    27831812751360*a*b^2 +
    55663625502720*a*b*c +
    17495566836376500*a*b +
    1935875565325260*a*c +
    91481243434605630*a +
    333211495983210*b^2 +
    666422991966420*b*c +
    64020072537060030*b +
    7434271723391730*c +
    214632875797346700
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    7013928574530*b^2 +
    14027857149060*b*c +
    576750231953568*b +
    89850263568120*c +
    1941295115823282
def slopeLo (b : ℕ) : ℕ :=
    3111503516069897484*b +
    27804296750350684977
def interceptLo (b : ℕ) : ℕ :=
    1556010589944059820*b^2 +
    233698265801357125554*b +
    662062153006826702136
def gHi0 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    10213690114975*a +
    3290026803497*b +
    35786689809711
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    5170944647626752*a^2 +
    10341889295253504*a*b +
    487338751262676880*a +
    165040904570623508*b +
    1707630708787091034
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452411594856344*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440911826888*a*b +
    9712390124912171688*a*c +
    459106978481333147466*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307046886635762*b +
    37302382819777725828*c +
    1077166458559497732588
def gHi1 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    96579108807617*a +
    3290026803497*b +
    3290026803497*c +
    318437624737173
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    5170944647626752*a^2 +
    10341889295253504*a*b +
    10341889295253504*a*c +
    4794752814895441148*a +
    165040904570623508*b +
    165040904570623508*c +
    15798959409661043232
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452411594856344*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440911826888*a*b +
    9712390124912171688*a*c +
    459106978481333147466*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307046886635762*b +
    37302382819777725828*c +
    1077166458559497732588
def gHi2 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    96579108807617*a +
    103080787968*b^2 +
    206161575936*b*c +
    96579108807617*b +
    10059068933023*c +
    436983500485317
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    5170944647626752*a^2 +
    10341889295253504*a*b +
    10341889295253504*a*c +
    4794752814895441148*a +
    5170944647626752*b^2 +
    10341889295253504*b*c +
    4794752814895441148*b +
    479582334291236752*c +
    21670632130804056048
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452411594856344*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440911826888*a*b +
    9712390124912171688*a*c +
    459106978481333147466*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307046886635762*b +
    37302382819777725828*c +
    1077166458559497732588
def conductorHi (a b c : ℕ) : ℕ :=
    532697056956*a^3 +
    1598091170868*a^2*b +
    1598091170868*a^2*c +
    98640496544814*a^2 +
    1598091170868*a*b^2 +
    3196182341736*a*b*c +
    197280993089628*a*b +
    34981003627812*a*c +
    1126154676386520*a +
    8612019745398*b^2 +
    17224039490796*b*c +
    772433133872328*b +
    123233176025064*c +
    2969341992721944
def slopeHi (a b : ℕ) : ℕ :=
    139644935389844532*a^2 +
    279289870779689064*a*b +
    9715251191903705340*a +
    3344245607750028660*b +
    37310080983089256441
def interceptHi (a b : ℕ) : ℕ :=
    46548311796614844*a^3 +
    139644935389844532*a^2*b +
    43910280531191414880*a^2 +
    139644935389844532*a*b^2 +
    87802025357923907400*a*b +
    459186130983247717464*a +
    1672381635784125408*b^2 +
    321290824200115899078*b +
    1077338003281328156652
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G16

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G17
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source28,source28,source28]
def scale : ℕ := 15
def denominator : ℕ := 11289150
def gLo0 (b c : ℕ) : ℕ :=
    4595731333555*b +
    37496182803960
def identitySlackLo0 (b c : ℕ) : ℕ :=
    230540266616453020*b +
    1776705182240645190
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160095021892338*b +
    67671072422978742294*c +
    1926796317239312821788
def gLo1 (b c : ℕ) : ℕ :=
    4595731333555*b +
    4595731333555*c +
    386901582053470
def identitySlackLo1 (b c : ℕ) : ℕ :=
    230540266616453020*b +
    230540266616453020*c +
    19200024298255860580
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160095021892338*b +
    67671072422978742294*c +
    1926796317239312821788
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    168401395793532*b +
    14405689214281*c +
    595095629789680
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8618241079377920*b^2 +
    17236482158755840*b*c +
    8364284953036975848*b +
    680945660970310384*c +
    29518766192416961020
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160095021892338*b +
    67671072422978742294*c +
    1926796317239312821788
def fullSlackLo (b c : ℕ) : ℕ :=
    766670291009250*b^2 +
    1533340582018500*b*c +
    135194594151236400*b +
    13485706967086950*c +
    383863643083065000
def fullSlackHi (a b c : ℕ) : ℕ :=
    25770196992000*a^3 +
    77310590976000*a^2*b +
    77310590976000*a^2*c +
    25466370944965800*a^2 +
    77310590976000*a*b^2 +
    154621181952000*a*b*c +
    50932741889931600*a*b +
    4772685211644300*a*c +
    266420861409072600*a +
    831095783489250*b^2 +
    1662191566978500*b*c +
    186011369958096000*b +
    18142426095659250*c +
    624818133153955800
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    11097977276070*b^2 +
    22195954552140*b*c +
    1002742834661028*b +
    136018273869864*c +
    3386634464771388
def slopeLo (b : ℕ) : ℕ :=
    7695492586279908540*b +
    67691872524519043719
def interceptLo (b : ℕ) : ℕ :=
    3848789970192821520*b^2 +
    678591077608287179163*b +
    1927272960692010309138
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    15006993810761*a +
    4853433303475*b +
    52245473334081
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    711109504748133104*a +
    243467628235519900*b +
    2474887259618753334
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140686705992438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264201179894976*a*b +
    23943378800113756068*a*c +
    1337265026598298537926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521604676401934*b +
    91033574432984436882*c +
    3136239227967229161036
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    168744998420092*a +
    4853433303475*b +
    4853433303475*c +
    555388877192922
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    17236482158755840*a*c +
    8381521435195731688*a +
    243467628235519900*b +
    243467628235519900*c +
    27568618306081567308
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140686705992438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264201179894976*a*b +
    23943378800113756068*a*c +
    1337265026598298537926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521604676401934*b +
    91033574432984436882*c +
    3136239227967229161036
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    168744998420092*a +
    171801313280*b^2 +
    343602626560*b*c +
    168744998420092*b +
    14749291840841*c +
    763668826896492
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    17236482158755840*a*c +
    8381521435195731688*a +
    8618241079377920*b^2 +
    17236482158755840*b*c +
    8381521435195731688*b +
    698182143129066224*c +
    37891669386533314788
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140686705992438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264201179894976*a*b +
    23943378800113756068*a*c +
    1337265026598298537926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521604676401934*b +
    91033574432984436882*c +
    3136239227967229161036
def conductorHi (a b c : ℕ) : ℕ :=
    887828428260*a^3 +
    2663485284780*a^2*b +
    2663485284780*a^2*c +
    171710838040968*a^2 +
    2663485284780*a*b^2 +
    5326970569560*a*b*c +
    343421676081936*a*b +
    54513489151548*a*c +
    1964644586239536*a +
    13761462560850*b^2 +
    27522925121700*b*c +
    1343501025458184*b +
    187868277736632*c +
    5180456041398216
def slopeHi (a b : ℕ) : ℕ :=
    387900822648267180*a^2 +
    775801645296534360*a*b +
    23955199410343759068*a +
    8341994845188782100*b +
    91065221046172065207
def interceptHi (a b : ℕ) : ℕ :=
    129300274216089060*a^3 +
    387900822648267180*a^2*b +
    127865871615238705488*a^2 +
    387900822648267180*a*b^2 +
    255643100259453885876*a*b +
    1337631629771556767376*a +
    4172041099647258300*b^2 +
    933652326979050327459*b +
    3137038717763234840886
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G17

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G18
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source29,source29,source29]
def scale : ℕ := 15
def denominator : ℕ := 11289150
def gLo0 (b c : ℕ) : ℕ :=
    4406747922849*b +
    36826146147760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    221060102801797236*b +
    1743093463419028390
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386805951136642*b +
    66455555295435346704*c +
    2088448379787017788512
def gLo1 (b c : ℕ) : ℕ :=
    4406747922849*b +
    4406747922849*c +
    418874213305030
def identitySlackLo1 (b c : ℕ) : ℕ :=
    221060102801797236*b +
    221060102801797236*c +
    20803899372359116420
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386805951136642*b +
    66455555295435346704*c +
    2088448379787017788512
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    182575151596482*b +
    14216705803575*c +
    645348379004680
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8618241079377920*b^2 +
    17236482158755840*b*c +
    9075297239136159648*b +
    671465497155654600*c +
    32039645104038221020
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386805951136642*b +
    66455555295435346704*c +
    2088448379787017788512
def fullSlackLo (b c : ℕ) : ℕ :=
    738322779403350*b^2 +
    1476645558806700*b*c +
    146311983927086100*b +
    13243463910627450*c +
    416069168982879000
def fullSlackHi (a b c : ℕ) : ℕ :=
    25770196992000*a^3 +
    77310590976000*a^2*b +
    77310590976000*a^2*c +
    27592434315408300*a^2 +
    77310590976000*a*b^2 +
    154621181952000*a*b*c +
    55184868630816600*a*b +
    4715990188432500*a*c +
    288841217176952100*a +
    802748271883350*b^2 +
    1605496543766700*b*c +
    201380886474830700*b +
    17843488015987950*c +
    677317951451206800
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    10920406171626*b^2 +
    21840812343252*b*c +
    1081939547243052*b +
    134242562825424*c +
    3665598669852912
def slopeLo (b : ℕ) : ℕ :=
    7411030621674814332*b +
    66476312876799420204
def interceptLo (b : ℕ) : ℕ :=
    3706558987890274416*b^2 +
    734390682345650612217*b +
    2088956910645488123862
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    14818010400055*a +
    4664449892769*b +
    51386453267175
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    701629340933477320*a +
    233987464420864116*b +
    2431795376982480750
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102924076435238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550111241370576*a*b +
    23658885911744132460*a*c +
    1449802304670819133026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034225667121838*b +
    89533564417071417684*c +
    3399756606350084280060
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    182918754223042*a +
    4664449892769*b +
    4664449892769*c +
    601535264247432
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    17236482158755840*a*c +
    9092533721294915488*a +
    233987464420864116*b +
    233987464420864116*c +
    29883505666284006948
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102924076435238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550111241370576*a*b +
    23658885911744132460*a*c +
    1449802304670819133026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034225667121838*b +
    89533564417071417684*c +
    3399756606350084280060
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    182918754223042*a +
    171801313280*b^2 +
    343602626560*b*c +
    182918754223042*b +
    14560308430135*c +
    828095331914442
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8618241079377920*a^2 +
    17236482158755840*a*b +
    17236482158755840*a*c +
    9092533721294915488*a +
    8618241079377920*b^2 +
    17236482158755840*b*c +
    9092533721294915488*b +
    688701979314410440*c +
    41123560584253758588
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102924076435238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550111241370576*a*b +
    23658885911744132460*a*c +
    1449802304670819133026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034225667121838*b +
    89533564417071417684*c +
    3399756606350084280060
def conductorHi (a b c : ℕ) : ℕ :=
    887828428260*a^3 +
    2663485284780*a^2*b +
    2663485284780*a^2*c +
    185028670874268*a^2 +
    2663485284780*a*b^2 +
    5326970569560*a*b*c +
    370057341748536*a*b +
    54158346942660*a*c +
    2124458580239136*a +
    13583891456406*b^2 +
    27167782912812*b*c +
    1449333403706808*b +
    185737424483304*c +
    5605916407646040
def slopeHi (a b : ℕ) : ℕ :=
    387900822648267180*a^2 +
    775801645296534360*a*b +
    23670691060091870760*a +
    8057532880583687892*b +
    89565153048200553384
def interceptHi (a b : ℕ) : ℕ :=
    129300274216089060*a^3 +
    387900822648267180*a^2*b +
    138540153134948853288*a^2 +
    387900822648267180*a*b^2 +
    276984705451855066476*a*b +
    1450191519938090120976*a +
    4029810117344711196*b^2 +
    1010793536908814941113*b +
    3400608276363535861410
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G18

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G19
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source30,source30,source30]
def scale : ℕ := 21
def denominator : ℕ := 22126734
def gLo0 (b c : ℕ) : ℕ :=
    6056057045565*b +
    49049989550670
def identitySlackLo0 (b c : ℕ) : ℕ :=
    303796045633722660*b +
    2314589011107723930
def helperSlackLo0 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792400512548440*b +
    124092480563104145490*c +
    3865958020545410449122
def gLo1 (b c : ℕ) : ℕ :=
    6056057045565*b +
    6056057045565*c +
    553937570150300
def identitySlackLo1 (b c : ℕ) : ℕ :=
    303796045633722660*b +
    303796045633722660*c +
    27495814939595477300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792400512548440*b +
    124092480563104145490*c +
    3865958020545410449122
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    241374761408913*b +
    18863979366122*c +
    853033970394692
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12065537511129088*b^2 +
    24131075022258176*b*c +
    11991559799547042972*b +
    887910795037309628*c +
    42324540718385764388
def helperSlackLo2 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792400512548440*b +
    124092480563104145490*c +
    3865958020545410449122
def fullSlackLo (b c : ℕ) : ℕ :=
    1423300737881610*b^2 +
    2846601475763220*b*c +
    270936557369915010*b +
    24728348765434860*c +
    770065526453469960
def fullSlackHi (a b c : ℕ) : ℕ :=
    50509586104320*a^3 +
    151528758312960*a^2*b +
    151528758312960*a^2*c +
    51092776584706290*a^2 +
    151528758312960*a*b^2 +
    303057516625920*a*b*c +
    102185553169412580*a*b +
    8806789090596840*a*c +
    534614756892839910*a +
    1549574703142410*b^2 +
    3099149406284820*b*c +
    372894817016506470*b +
    33307844333210580*c +
    1253587505990900220
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
def conductorLo (b c : ℕ) : ℕ :=
    15182025977610*b^2 +
    30364051955220*b*c +
    1434062570501808*b +
    181653570858276*c +
    4850618779686114
def slopeLo (b : ℕ) : ℕ :=
    14287932644741604972*b +
    124145272388171975436
def interceptLo (b : ℕ) : ℕ :=
    7146648340468437348*b^2 +
    1360132654565842996575*b +
    3867270059426916617700
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19705805801194*a +
    6416839803453*b +
    68395010758968
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    930140176326261436*a +
    321894351900416292*b +
    3226630789115950422
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131846514334686*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259226285710088*a*b +
    44179544752331505780*a*c +
    2683853783851374603324*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534833372859892*b +
    167134053793581908862*c +
    6293324215197875135088
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    241855805086097*a +
    6416839803453*b +
    6416839803453*c +
    795432590643501
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    12015690874569301148*a +
    321894351900416292*b +
    321894351900416292*c +
    39493407415846743504
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131846514334686*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259226285710088*a*b +
    44179544752331505780*a*c +
    2683853783851374603324*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534833372859892*b +
    167134053793581908862*c +
    6293324215197875135088
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    241855805086097*a +
    240521838592*b^2 +
    481043677184*b*c +
    241855805086097*b +
    19345023043306*c +
    1094649253642197
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12065537511129088*a^2 +
    24131075022258176*a*b +
    24131075022258176*a*c +
    12015690874569301148*a +
    12065537511129088*b^2 +
    24131075022258176*b*c +
    12015690874569301148*b +
    912041870059567804*c +
    54328166055443936448
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131846514334686*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259226285710088*a*b +
    44179544752331505780*a*c +
    2683853783851374603324*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534833372859892*b +
    167134053793581908862*c +
    6293324215197875135088
def conductorHi (a b c : ℕ) : ℕ :=
    1242959799564*a^3 +
    3728879398692*a^2*b +
    3728879398692*a^2*c +
    245669035059342*a^2 +
    3728879398692*a*b^2 +
    7457758797384*a*b*c +
    491338070118684*a*b +
    73868403570840*a*c +
    2813788762359192*a +
    18910905376302*b^2 +
    37821810752604*b*c +
    1921671761221800*b +
    251793095030424*c +
    7419981466785528
def slopeHi (a b : ℕ) : ℕ :=
    760284120838844196*a^2 +
    1520568241677688392*a*b +
    44209440923286966240*a +
    15555074089099478196*b +
    167214287061176855496
def interceptHi (a b : ℕ) : ℕ :=
    253428040279614732*a^3 +
    760284120838844196*a^2*b +
    256605889017392090868*a^2 +
    760284120838844196*a*b^2 +
    512964395958727759380*a*b +
    2684856051685835036298*a +
    7780219062647373960*b^2 +
    1871956624274288669775*b +
    6295520219471392324230
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G19
end MergedPart0
section MergedPart1
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
    10587614795930702040*b +
    87188447990722107680
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10110092451521858794692*b^2 +
    20261755113028677105384*b*c +
    2394620472876871267642884*b +
    187189713479449766250396*c +
    6380530718214166336898814
def gLo1 (b c : ℕ) : ℕ :=
    211060019056110*b +
    212004936109640*c +
    21565467406099540
def identitySlackLo1 (b c : ℕ) : ℕ :=
    10587614795930702040*b +
    10635015615003980960*c +
    1070133733782610448560
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10107837738002491181892*b^2 +
    20259500399509309492584*b*c +
    2394601295288979948913284*b +
    187174039580710958984796*c +
    6380490914597017773401214
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    11601992045155085*b +
    720542160717800*c +
    36047048873537170
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482621500445163520*b^2 +
    965243000890327040*b*c +
    577331779682372933540*b +
    33810002314854344000*c +
    1789581944792375991880
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10103231334038191757892*b^2 +
    20254893995545010068584*b*c +
    2394547030169299690993284*b +
    187147273942781282610396*c +
    6380334508516200287321214
def fullSlackLo (b c : ℕ) : ℕ :=
    2015350173372060000*b^2 +
    4038637649993772000*b*c +
    477065976793310478000*b +
    37296726177012120000*c +
    1270686117305399676000
def fullSlackHi (a b c : ℕ) : ℕ :=
    80815337766912000*a^3 +
    242446013300736000*a^2*b +
    242446013300736000*a^2*c +
    79706968139719569600*a^2 +
    242446013300736000*a*b^2 +
    484892026601472000*a*b*c +
    177810224021157579600*a*b +
    13554300845278468800*a*c +
    857269110599019871200*a +
    2217388517789340000*b^2 +
    4442714338828332000*b*c +
    654512531177954265600*b +
    50487357385776796800*c +
    2048248258531574601600
def fullSlack : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => fullSlackLo b c
  | a+1, b, c => fullSlackHi a b c
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
    482621500445163520*a^2 +
    965243000890327040*a*b +
    35707741170334843568*a +
    11311547046598447320*b +
    122172253228335553488
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    401993413389517860960*a^3 +
    1209471409488864725280*a^2*b +
    1212962578809175867680*a^2*c +
    400240286973271660136886*a^2 +
    1212962578809175867680*a*b^2 +
    2429416326938662877760*a*b*c +
    892458730512681463431132*a*b +
    68005121794272047306916*a*c +
    4304640517222586414006952*a +
    11120313592475182527972*b^2 +
    22285688564255635714344*b*c +
    3285261504572954679174336*b +
    253373645287803450515232*c +
    10284927452814075642818640
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    9431199537275964*a +
    225491329371630*b +
    226436246425160*c +
    30982235559659664
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    468436144317124707696*a +
    11311547046598447320*b +
    11358947865671726240*c +
    1537845942167013758496
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401266086447786372960*a^3 +
    1208016755605401749280*a^2*b +
    1212235251867444379680*a^2*c +
    400229809069016658143286*a^2 +
    1212235251867444379680*a*b^2 +
    2428688999996931389760*a*b*c +
    892445270567965362336732*a*b +
    67996175671963898916516*a*c +
    4304590448425775986646952*a +
    11117331552014083427172*b^2 +
    22282706523794536613544*b*c +
    3285230321694230722326336*b +
    253349752593698226347232*c +
    10284847330977429922466640
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
    482621500445163520*a^2 +
    965243000890327040*a*b +
    965243000890327040*a*c +
    468436144317124707696*a +
    482621500445163520*b^2 +
    965243000890327040*b*c +
    578297022683263260580*b +
    34775245315744671040*c +
    2257535467609055536056
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    399811432564323396960*a^3 +
    1205107447838475797280*a^2*b +
    1210780597983981403680*a^2*c +
    400203325575749494847286*a^2 +
    1210780597983981403680*a*b^2 +
    2427234346113468413760*a*b*c +
    892412726016850436640732*a*b +
    67980029012007757706916*a*c +
    4304436300796194763382952*a +
    11111270494166321027172*b^2 +
    22276645465946774213544*b*c +
    3285146421331202464662336*b +
    253308294949695871739232*c +
    10284561806106414913442640
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
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50164 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,fullSlack,fullSlackLo,fullSlackHi,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G20
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberCount6815
open scoped BigOperators
open RCN095 RCN130 RCN146 RCN260 RCN327
open MovingFiberProfile6815 MovingFiberArithmeticBase6815 MovingFiberCatalog6815 MovingFiberRegularData6815
open HFreeDirArith6815 HFreeDirChain6815
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Receipt (g : Fin 21) where
  scale : ℕ
  denominator : ℕ
  full : ℕ → ℕ → ℕ → ℕ
  rounded : ℕ → ℕ → ℕ → ℕ
  slope : ℕ → ℕ → ℕ
  intercept : ℕ → ℕ → ℕ
  rounded_formula : ∀ a b c, rounded a b c=slope a b*c+intercept a b
  positive : 0 < scale
  divides : ∀ j : Fin 3, 3*(groups g j).d ∣ scale
  identity : ∀ (f : FlagDegree) (a b c : ℕ),
    scale*131073*80910*identityDegree f a b c ≤ 50164*graphDir (groups g) scale f a b c
  helper : ∀ (a b c : ℕ) (j : Fin 3),
    MovingFiberArithmeticBase6815.helper (groups g j) a b c/50164 ≤ full a b c/denominator
  retained : ∀ a b c,
    graphDir (groups g) scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (groups g j) a b c/50164) ≤ full a b c/denominator
  rounded_bound : ∀ a b c, full a b c/denominator ≤ rounded a b c

def receipt0 : Receipt 0 where
  scale := MovingFiberArithmetic6815.G0.scale
  denominator := MovingFiberArithmetic6815.G0.denominator
  full := MovingFiberArithmetic6815.G0.full
  rounded := MovingFiberArithmetic6815.G0.rounded
  slope := fun a b => MovingFiberArithmetic6815.G0.slope a b/MovingFiberArithmetic6815.G0.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G0.intercept a b/MovingFiberArithmetic6815.G0.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G0.positive
  divides := MovingFiberArithmetic6815.G0.divides
  identity := MovingFiberArithmetic6815.G0.identity_absorption
  helper := MovingFiberArithmetic6815.G0.helper_cap
  retained := MovingFiberArithmetic6815.G0.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G0.full_cap_rounded

def receipt1 : Receipt 1 where
  scale := MovingFiberArithmetic6815.G1.scale
  denominator := MovingFiberArithmetic6815.G1.denominator
  full := MovingFiberArithmetic6815.G1.full
  rounded := MovingFiberArithmetic6815.G1.rounded
  slope := fun a b => MovingFiberArithmetic6815.G1.slope a b/MovingFiberArithmetic6815.G1.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G1.intercept a b/MovingFiberArithmetic6815.G1.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G1.positive
  divides := MovingFiberArithmetic6815.G1.divides
  identity := MovingFiberArithmetic6815.G1.identity_absorption
  helper := MovingFiberArithmetic6815.G1.helper_cap
  retained := MovingFiberArithmetic6815.G1.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G1.full_cap_rounded

def receipt2 : Receipt 2 where
  scale := MovingFiberArithmetic6815.G2.scale
  denominator := MovingFiberArithmetic6815.G2.denominator
  full := MovingFiberArithmetic6815.G2.full
  rounded := MovingFiberArithmetic6815.G2.rounded
  slope := fun a b => MovingFiberArithmetic6815.G2.slope a b/MovingFiberArithmetic6815.G2.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G2.intercept a b/MovingFiberArithmetic6815.G2.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G2.positive
  divides := MovingFiberArithmetic6815.G2.divides
  identity := MovingFiberArithmetic6815.G2.identity_absorption
  helper := MovingFiberArithmetic6815.G2.helper_cap
  retained := MovingFiberArithmetic6815.G2.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G2.full_cap_rounded

def receipt3 : Receipt 3 where
  scale := MovingFiberArithmetic6815.G3.scale
  denominator := MovingFiberArithmetic6815.G3.denominator
  full := MovingFiberArithmetic6815.G3.full
  rounded := MovingFiberArithmetic6815.G3.rounded
  slope := fun a b => MovingFiberArithmetic6815.G3.slope a b/MovingFiberArithmetic6815.G3.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G3.intercept a b/MovingFiberArithmetic6815.G3.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G3.positive
  divides := MovingFiberArithmetic6815.G3.divides
  identity := MovingFiberArithmetic6815.G3.identity_absorption
  helper := MovingFiberArithmetic6815.G3.helper_cap
  retained := MovingFiberArithmetic6815.G3.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G3.full_cap_rounded

def receipt4 : Receipt 4 where
  scale := MovingFiberArithmetic6815.G4.scale
  denominator := MovingFiberArithmetic6815.G4.denominator
  full := MovingFiberArithmetic6815.G4.full
  rounded := MovingFiberArithmetic6815.G4.rounded
  slope := fun a b => MovingFiberArithmetic6815.G4.slope a b/MovingFiberArithmetic6815.G4.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G4.intercept a b/MovingFiberArithmetic6815.G4.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G4.positive
  divides := MovingFiberArithmetic6815.G4.divides
  identity := MovingFiberArithmetic6815.G4.identity_absorption
  helper := MovingFiberArithmetic6815.G4.helper_cap
  retained := MovingFiberArithmetic6815.G4.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G4.full_cap_rounded

def receipt5 : Receipt 5 where
  scale := MovingFiberArithmetic6815.G5.scale
  denominator := MovingFiberArithmetic6815.G5.denominator
  full := MovingFiberArithmetic6815.G5.full
  rounded := MovingFiberArithmetic6815.G5.rounded
  slope := fun a b => MovingFiberArithmetic6815.G5.slope a b/MovingFiberArithmetic6815.G5.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G5.intercept a b/MovingFiberArithmetic6815.G5.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G5.positive
  divides := MovingFiberArithmetic6815.G5.divides
  identity := MovingFiberArithmetic6815.G5.identity_absorption
  helper := MovingFiberArithmetic6815.G5.helper_cap
  retained := MovingFiberArithmetic6815.G5.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G5.full_cap_rounded

def receipt6 : Receipt 6 where
  scale := MovingFiberArithmetic6815.G6.scale
  denominator := MovingFiberArithmetic6815.G6.denominator
  full := MovingFiberArithmetic6815.G6.full
  rounded := MovingFiberArithmetic6815.G6.rounded
  slope := fun a b => MovingFiberArithmetic6815.G6.slope a b/MovingFiberArithmetic6815.G6.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G6.intercept a b/MovingFiberArithmetic6815.G6.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G6.positive
  divides := MovingFiberArithmetic6815.G6.divides
  identity := MovingFiberArithmetic6815.G6.identity_absorption
  helper := MovingFiberArithmetic6815.G6.helper_cap
  retained := MovingFiberArithmetic6815.G6.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G6.full_cap_rounded

def receipt7 : Receipt 7 where
  scale := MovingFiberArithmetic6815.G7.scale
  denominator := MovingFiberArithmetic6815.G7.denominator
  full := MovingFiberArithmetic6815.G7.full
  rounded := MovingFiberArithmetic6815.G7.rounded
  slope := fun a b => MovingFiberArithmetic6815.G7.slope a b/MovingFiberArithmetic6815.G7.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G7.intercept a b/MovingFiberArithmetic6815.G7.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G7.positive
  divides := MovingFiberArithmetic6815.G7.divides
  identity := MovingFiberArithmetic6815.G7.identity_absorption
  helper := MovingFiberArithmetic6815.G7.helper_cap
  retained := MovingFiberArithmetic6815.G7.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G7.full_cap_rounded

def receipt8 : Receipt 8 where
  scale := MovingFiberArithmetic6815.G8.scale
  denominator := MovingFiberArithmetic6815.G8.denominator
  full := MovingFiberArithmetic6815.G8.full
  rounded := MovingFiberArithmetic6815.G8.rounded
  slope := fun a b => MovingFiberArithmetic6815.G8.slope a b/MovingFiberArithmetic6815.G8.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G8.intercept a b/MovingFiberArithmetic6815.G8.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G8.positive
  divides := MovingFiberArithmetic6815.G8.divides
  identity := MovingFiberArithmetic6815.G8.identity_absorption
  helper := MovingFiberArithmetic6815.G8.helper_cap
  retained := MovingFiberArithmetic6815.G8.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G8.full_cap_rounded

def receipt9 : Receipt 9 where
  scale := MovingFiberArithmetic6815.G9.scale
  denominator := MovingFiberArithmetic6815.G9.denominator
  full := MovingFiberArithmetic6815.G9.full
  rounded := MovingFiberArithmetic6815.G9.rounded
  slope := fun a b => MovingFiberArithmetic6815.G9.slope a b/MovingFiberArithmetic6815.G9.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G9.intercept a b/MovingFiberArithmetic6815.G9.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G9.positive
  divides := MovingFiberArithmetic6815.G9.divides
  identity := MovingFiberArithmetic6815.G9.identity_absorption
  helper := MovingFiberArithmetic6815.G9.helper_cap
  retained := MovingFiberArithmetic6815.G9.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G9.full_cap_rounded

def receipt10 : Receipt 10 where
  scale := MovingFiberArithmetic6815.G10.scale
  denominator := MovingFiberArithmetic6815.G10.denominator
  full := MovingFiberArithmetic6815.G10.full
  rounded := MovingFiberArithmetic6815.G10.rounded
  slope := fun a b => MovingFiberArithmetic6815.G10.slope a b/MovingFiberArithmetic6815.G10.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G10.intercept a b/MovingFiberArithmetic6815.G10.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G10.positive
  divides := MovingFiberArithmetic6815.G10.divides
  identity := MovingFiberArithmetic6815.G10.identity_absorption
  helper := MovingFiberArithmetic6815.G10.helper_cap
  retained := MovingFiberArithmetic6815.G10.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G10.full_cap_rounded

def receipt11 : Receipt 11 where
  scale := MovingFiberArithmetic6815.G11.scale
  denominator := MovingFiberArithmetic6815.G11.denominator
  full := MovingFiberArithmetic6815.G11.full
  rounded := MovingFiberArithmetic6815.G11.rounded
  slope := fun a b => MovingFiberArithmetic6815.G11.slope a b/MovingFiberArithmetic6815.G11.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G11.intercept a b/MovingFiberArithmetic6815.G11.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G11.positive
  divides := MovingFiberArithmetic6815.G11.divides
  identity := MovingFiberArithmetic6815.G11.identity_absorption
  helper := MovingFiberArithmetic6815.G11.helper_cap
  retained := MovingFiberArithmetic6815.G11.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G11.full_cap_rounded

def receipt12 : Receipt 12 where
  scale := MovingFiberArithmetic6815.G12.scale
  denominator := MovingFiberArithmetic6815.G12.denominator
  full := MovingFiberArithmetic6815.G12.full
  rounded := MovingFiberArithmetic6815.G12.rounded
  slope := fun a b => MovingFiberArithmetic6815.G12.slope a b/MovingFiberArithmetic6815.G12.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G12.intercept a b/MovingFiberArithmetic6815.G12.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G12.positive
  divides := MovingFiberArithmetic6815.G12.divides
  identity := MovingFiberArithmetic6815.G12.identity_absorption
  helper := MovingFiberArithmetic6815.G12.helper_cap
  retained := MovingFiberArithmetic6815.G12.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G12.full_cap_rounded

def receipt13 : Receipt 13 where
  scale := MovingFiberArithmetic6815.G13.scale
  denominator := MovingFiberArithmetic6815.G13.denominator
  full := MovingFiberArithmetic6815.G13.full
  rounded := MovingFiberArithmetic6815.G13.rounded
  slope := fun a b => MovingFiberArithmetic6815.G13.slope a b/MovingFiberArithmetic6815.G13.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G13.intercept a b/MovingFiberArithmetic6815.G13.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G13.positive
  divides := MovingFiberArithmetic6815.G13.divides
  identity := MovingFiberArithmetic6815.G13.identity_absorption
  helper := MovingFiberArithmetic6815.G13.helper_cap
  retained := MovingFiberArithmetic6815.G13.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G13.full_cap_rounded

def receipt14 : Receipt 14 where
  scale := MovingFiberArithmetic6815.G14.scale
  denominator := MovingFiberArithmetic6815.G14.denominator
  full := MovingFiberArithmetic6815.G14.full
  rounded := MovingFiberArithmetic6815.G14.rounded
  slope := fun a b => MovingFiberArithmetic6815.G14.slope a b/MovingFiberArithmetic6815.G14.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G14.intercept a b/MovingFiberArithmetic6815.G14.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G14.positive
  divides := MovingFiberArithmetic6815.G14.divides
  identity := MovingFiberArithmetic6815.G14.identity_absorption
  helper := MovingFiberArithmetic6815.G14.helper_cap
  retained := MovingFiberArithmetic6815.G14.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G14.full_cap_rounded

def receipt15 : Receipt 15 where
  scale := MovingFiberArithmetic6815.G15.scale
  denominator := MovingFiberArithmetic6815.G15.denominator
  full := MovingFiberArithmetic6815.G15.full
  rounded := MovingFiberArithmetic6815.G15.rounded
  slope := fun a b => MovingFiberArithmetic6815.G15.slope a b/MovingFiberArithmetic6815.G15.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G15.intercept a b/MovingFiberArithmetic6815.G15.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G15.positive
  divides := MovingFiberArithmetic6815.G15.divides
  identity := MovingFiberArithmetic6815.G15.identity_absorption
  helper := MovingFiberArithmetic6815.G15.helper_cap
  retained := MovingFiberArithmetic6815.G15.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G15.full_cap_rounded

def receipt16 : Receipt 16 where
  scale := MovingFiberArithmetic6815.G16.scale
  denominator := MovingFiberArithmetic6815.G16.denominator
  full := MovingFiberArithmetic6815.G16.full
  rounded := MovingFiberArithmetic6815.G16.rounded
  slope := fun a b => MovingFiberArithmetic6815.G16.slope a b/MovingFiberArithmetic6815.G16.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G16.intercept a b/MovingFiberArithmetic6815.G16.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G16.positive
  divides := MovingFiberArithmetic6815.G16.divides
  identity := MovingFiberArithmetic6815.G16.identity_absorption
  helper := MovingFiberArithmetic6815.G16.helper_cap
  retained := MovingFiberArithmetic6815.G16.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G16.full_cap_rounded

def receipt17 : Receipt 17 where
  scale := MovingFiberArithmetic6815.G17.scale
  denominator := MovingFiberArithmetic6815.G17.denominator
  full := MovingFiberArithmetic6815.G17.full
  rounded := MovingFiberArithmetic6815.G17.rounded
  slope := fun a b => MovingFiberArithmetic6815.G17.slope a b/MovingFiberArithmetic6815.G17.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G17.intercept a b/MovingFiberArithmetic6815.G17.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G17.positive
  divides := MovingFiberArithmetic6815.G17.divides
  identity := MovingFiberArithmetic6815.G17.identity_absorption
  helper := MovingFiberArithmetic6815.G17.helper_cap
  retained := MovingFiberArithmetic6815.G17.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G17.full_cap_rounded

def receipt18 : Receipt 18 where
  scale := MovingFiberArithmetic6815.G18.scale
  denominator := MovingFiberArithmetic6815.G18.denominator
  full := MovingFiberArithmetic6815.G18.full
  rounded := MovingFiberArithmetic6815.G18.rounded
  slope := fun a b => MovingFiberArithmetic6815.G18.slope a b/MovingFiberArithmetic6815.G18.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G18.intercept a b/MovingFiberArithmetic6815.G18.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G18.positive
  divides := MovingFiberArithmetic6815.G18.divides
  identity := MovingFiberArithmetic6815.G18.identity_absorption
  helper := MovingFiberArithmetic6815.G18.helper_cap
  retained := MovingFiberArithmetic6815.G18.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G18.full_cap_rounded

def receipt19 : Receipt 19 where
  scale := MovingFiberArithmetic6815.G19.scale
  denominator := MovingFiberArithmetic6815.G19.denominator
  full := MovingFiberArithmetic6815.G19.full
  rounded := MovingFiberArithmetic6815.G19.rounded
  slope := fun a b => MovingFiberArithmetic6815.G19.slope a b/MovingFiberArithmetic6815.G19.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G19.intercept a b/MovingFiberArithmetic6815.G19.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G19.positive
  divides := MovingFiberArithmetic6815.G19.divides
  identity := MovingFiberArithmetic6815.G19.identity_absorption
  helper := MovingFiberArithmetic6815.G19.helper_cap
  retained := MovingFiberArithmetic6815.G19.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G19.full_cap_rounded

def receipt20 : Receipt 20 where
  scale := MovingFiberArithmetic6815.G20.scale
  denominator := MovingFiberArithmetic6815.G20.denominator
  full := MovingFiberArithmetic6815.G20.full
  rounded := MovingFiberArithmetic6815.G20.rounded
  slope := fun a b => MovingFiberArithmetic6815.G20.slope a b/MovingFiberArithmetic6815.G20.denominator+1
  intercept := fun a b => MovingFiberArithmetic6815.G20.intercept a b/MovingFiberArithmetic6815.G20.denominator+1
  rounded_formula := by intro a b c; rfl
  positive := MovingFiberArithmetic6815.G20.positive
  divides := MovingFiberArithmetic6815.G20.divides
  identity := MovingFiberArithmetic6815.G20.identity_absorption
  helper := MovingFiberArithmetic6815.G20.helper_cap
  retained := MovingFiberArithmetic6815.G20.retained_cap
  rounded_bound := MovingFiberArithmetic6815.G20.full_cap_rounded
def receipt (g : Fin 21) : Receipt g := by
  exact (Fin.cases (motive := fun j : Fin 21 => Receipt (j)) receipt0 (Fin.cases (motive := fun j : Fin 20 => Receipt (j.succ)) receipt1 (Fin.cases (motive := fun j : Fin 19 => Receipt (j.succ.succ)) receipt2 (Fin.cases (motive := fun j : Fin 18 => Receipt (j.succ.succ.succ)) receipt3 (Fin.cases (motive := fun j : Fin 17 => Receipt (j.succ.succ.succ.succ)) receipt4 (Fin.cases (motive := fun j : Fin 16 => Receipt (j.succ.succ.succ.succ.succ)) receipt5 (Fin.cases (motive := fun j : Fin 15 => Receipt (j.succ.succ.succ.succ.succ.succ)) receipt6 (Fin.cases (motive := fun j : Fin 14 => Receipt (j.succ.succ.succ.succ.succ.succ.succ)) receipt7 (Fin.cases (motive := fun j : Fin 13 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ)) receipt8 (Fin.cases (motive := fun j : Fin 12 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt9 (Fin.cases (motive := fun j : Fin 11 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt10 (Fin.cases (motive := fun j : Fin 10 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt11 (Fin.cases (motive := fun j : Fin 9 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt12 (Fin.cases (motive := fun j : Fin 8 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt13 (Fin.cases (motive := fun j : Fin 7 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt14 (Fin.cases (motive := fun j : Fin 6 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt15 (Fin.cases (motive := fun j : Fin 5 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt16 (Fin.cases (motive := fun j : Fin 4 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt17 (Fin.cases (motive := fun j : Fin 3 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt18 (Fin.cases (motive := fun j : Fin 2 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt19 (Fin.cases (motive := fun j : Fin 1 => Receipt (j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) receipt20 (fun i => Fin.elim0 i)))))))))))))))))))))) g

def scales (g : Fin 21) : ℕ := (receipt g).scale
def denominators (g : Fin 21) : ℕ := (receipt g).denominator
def fulls (g : Fin 21) : ℕ → ℕ → ℕ → ℕ := (receipt g).full
def roundedCaps (g : Fin 21) : ℕ → ℕ → ℕ → ℕ := (receipt g).rounded
def sourceLimit (g : Fin 21) : ℕ := Finset.univ.sup (fun j : Fin 3 => (groups g j).L)

theorem scale_positive (g : Fin 21) : 0 < scales g := (receipt g).positive
theorem scale_divides (g : Fin 21) (j : Fin 3) : 3*(groups g j).d ∣ scales g := (receipt g).divides j
theorem identity_absorption (g : Fin 21) (f : FlagDegree) (a b c : ℕ) :
    scales g*131073*80910*identityDegree f a b c ≤ 50164*graphDir (groups g) (scales g) f a b c :=
  (receipt g).identity f a b c
theorem helper_cap (g : Fin 21) (a b c : ℕ) (j : Fin 3) :
    helper (groups g j) a b c/50164 ≤ fulls g a b c/denominators g := (receipt g).helper a b c j
theorem retained_cap (g : Fin 21) (a b c : ℕ) :
    graphDir (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c/scales g+
      (∑ j : Fin 3, coeff (groups g j) a b c/50164) ≤ fulls g a b c/denominators g :=
  (receipt g).retained a b c
theorem rounded_cap (g : Fin 21) (a b c : ℕ) :
    fulls g a b c/denominators g ≤ roundedCaps g a b c := (receipt g).rounded_bound a b c

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem bound_le_full (S : Data nodes u0 u1) (hown : Own S) (g : Fin 21) :
    boundDir S (groups g) (scales g) ≤
      fulls g (S.r-3) (S.y-S.r-2) (S.t-S.y)/denominators g := by
  obtain ⟨a,ha⟩ : ∃ a, S.r=a+3 := ⟨S.r-3,by have := S.rpos; omega⟩
  obtain ⟨b,hb⟩ : ∃ b, S.y=a+3+(b+2) := ⟨S.y-S.r-2,by have := S.ry; omega⟩
  obtain ⟨c,hc⟩ : ∃ c, S.t=a+3+(b+2)+c := ⟨S.t-S.y,by have := S.yt; omega⟩
  have hv : S.y-S.r=b+2 := by omega
  have hz : S.t-S.y=c := by omega
  have har : S.r-3=a := by omega
  have hbr : S.y-S.r-2=b := by omega
  have hp (R U T : ℕ) : AsymmetricHelper.leftRegularCountCap (S.pair R U T)=
      pairNumerator a b c U R T/50164 := by
    unfold AsymmetricHelper.leftRegularCountCap
    rw [pair_numerator S a b c ha hb hc]
    norm_num only [Data.pair,UnequalParameters.gap]
  have hcoeff (j : Fin 3) : coefficientCap S (groups g j)=coeff (groups g j) a b c/50164 := hp _ _ _
  have hhelper (j : Fin 3) : helperCap S (groups g j)=helper (groups g j) a b c/50164 := by
    unfold helperCap
    rw [hp,ha,hb,hc]
    have h1 : a+3-1=a+2 := by omega
    have h2 : a+3+(b+2)-1=a+b+4 := by omega
    have h3 : a+3+(b+2)+c-1=a+b+c+4 := by omega
    simp only [h1,h2,h3,helper]
  have hn : numberDir (groups g) (scales g) S.t S.y S.r (originalCumulativeFlag S.F)=
      graphDir (groups g) (scales g) ⟨c,b+2,a+3⟩ a b c := by
    rw [hown,hv,hz,hc,hb,ha,numberDir_coordinates]
  rw [har,hbr,hz]
  unfold boundDir
  apply max_le
  · apply Finset.sup_le
    intro j _
    rw [hhelper]
    exact helper_cap g a b c j
  · rw [hn]
    simp_rw [hcoeff]
    exact retained_cap g a b c

theorem hfree_stage_gap (S : Data nodes u0 u1) :
    ∀ (G : Finset K) (fl : FlagDegree) (S' : RCN159.ResidualStage (RCN135.polynomialEmbedding K) G
      ⇑nodes 2130706433 80909 fl w (LocatorHybridCells.cellSupport S.t S.y S.r)), S'.F = S.F →
      HFreeDir6813.HFreeStageDir S' := by
  intro G fl S' _
  haveI : CharP (RCN135.GenericField K) 2130706433 := RCN135.genericField_charP K 2130706433
  refine HFreeDir6813.hfree_stage_dir_of_gaps S' ?_
  have := S.tbound; have := S.yt; have := S.ry; have := S.rpos
  simp only [LocatorHybridCells.cellSupport, RCN198.support, LocatorHybridCells.cellA,
    LocatorHybridCells.cellB, LocatorHybridCells.cellS]
  omega

theorem count_group (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (g : Fin 21) (hL : sourceLimit g < S.t) :
    S.seeds.card ≤ roundedCaps g (S.r-3) (S.y-S.r-2) (S.t-S.y) := by
  obtain ⟨P,hP⟩ := exists_group nodes u0 u1 hI g
  have hLt (j : Fin 3) : (groups g j).L < RCN234.wt RCN156.residualTotalWeights S.F := by
    rw [own_total S hown]
    exact (Finset.le_sup (f := fun j : Fin 3 => (groups g j).L) (Finset.mem_univ j)).trans_lt hL
  have hid (f : FlagDegree) : scales g*131073*80910*
      identityCurveDegree f (LocatorHybridCells.cellA S.t S.y)
        (LocatorHybridCells.cellB S.y S.r) (LocatorHybridCells.cellS S.r) w ≤
        50164*numberDir (groups g) (scales g) S.t S.y S.r f := by
    obtain ⟨a,ha⟩ : ∃ a, S.r=a+3 := ⟨S.r-3,by have := S.rpos; omega⟩
    obtain ⟨b,hb⟩ : ∃ b, S.y=a+3+(b+2) := ⟨S.y-S.r-2,by have := S.ry; omega⟩
    obtain ⟨c,hc⟩ : ∃ c, S.t=a+3+(b+2)+c := ⟨S.t-S.y,by have := S.yt; omega⟩
    rw [ha,hb,hc,identity_coordinates,numberDir_coordinates]
    exact identity_absorption g f a b c
  have hcount := count_of_interpolants_dir S hI (groups g) (wellFormed g) (scales g)
    (scale_positive g) (scale_divides g) (hfree_stage_gap S) P hP hLt
    (fun j => (catalog_gates S g j).1) (fun j => (catalog_gates S g j).2) hid
  exact (hcount.trans (bound_le_full S hown g)).trans (rounded_cap g _ _ _)

end ProximityPrize.SubmissionLower.MovingFiberCount6815
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberCarrier6815

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorHybridCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (g : Fin 21) (p : FlagDegree) : Prop :=
  3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧ MovingFiberCount6815.sourceLimit g < p.all+p.yz+p.zOnly

def ledgerCap (g : Fin 21) (p : FlagDegree) : ℕ :=
  MovingFiberCount6815.roundedCaps g (p.all-3) (p.yz-2) p.zOnly

section Carrier
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def ofCarrier (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (h3 : 3 ≤ wt residualSWeights F)
    (hry : wt residualSWeights F+2 ≤ wt residualYSWeights F)
    (hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181235 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80909) :
    MovingFiberRegularData6815.Data nodes u0 u1 where
  D := D
  t := wt residualTotalWeights F
  y := wt residualYSWeights F
  r := wt residualSWeights F
  Dlow := hDlow
  Dchar := hDchar
  tbound := ht
  ybound := hy
  rbound := hr
  rpos := h3
  ry := hry
  yt := hyt
  F := F
  irreducible := hF
  rdegree := hrdegree
  box := by
    intro e he
    have hs := MvPolynomial.le_weightedTotalDegree residualSWeights he
    have ht := MvPolynomial.le_weightedTotalDegree residualTotalWeights he
    simp only [RCN081.weight_fin4,residualSWeights,residualTotalWeights,Fin.isValue,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Nat.mul_zero,Nat.mul_one,
      Nat.zero_add,Nat.add_zero] at hs ht
    change e 1+e 2+e 3 ≤ wt residualTotalWeights F at ht
    exact ⟨by omega,hs,(hbox he).2.2⟩
  support := by
    constructor <;> dsimp only [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega
  selected := selected
  seeds := seeds
  degree := hdegree
  agreement := hagreement
  solution := hsolution
  regular := hregular
  noPencil := hno

theorem carrier_count_le_ledger (g : Fin 21) (D L s : ℕ) (F : MvPolynomial (Fin 4) K)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hF : Irreducible F) (hrdegree : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w L s)
    (ht : wt residualTotalWeights F ≤ 7501) (hy : wt residualYSWeights F ≤ 142)
    (hr : wt residualSWeights F ≤ 31)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ seeds, 181235 ≤
      (Finset.univ.filter (fun i => (selected gamma).eval (nodes i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ seeds, specialization K (selected gamma) gamma F=0)
    (hregular : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma (pderiv (2:Fin 4) F)≠0)
    (hno : NoLargeSelectedPencil selected seeds w 80909)
    (hI : Fintype.card I=262144)
    (ha : Active g (originalCumulativeFlag F)) :
    seeds.card ≤ ledgerCap g (originalCumulativeFlag F) := by
  let p := originalCumulativeFlag F
  have ha' : 3 ≤ p.all ∧ 2 ≤ p.yz ∧ 3 ≤ p.zOnly ∧
      MovingFiberCount6815.sourceLimit g < p.all+p.yz+p.zOnly := ha
  have h3 : 3 ≤ wt residualSWeights F := ha'.1
  have hry : wt residualSWeights F+2 ≤ wt residualYSWeights F := by
    have hv : 2 ≤ wt residualYSWeights F-wt residualSWeights F := ha'.2.1
    omega
  have hyt : wt residualYSWeights F+2 ≤ wt residualTotalWeights F := by
    have hz : 3 ≤ wt residualTotalWeights F-wt residualYSWeights F := ha'.2.2.1
    omega
  have htotal : p.all+p.yz+p.zOnly = wt residualTotalWeights F := by
    change wt residualSWeights F+(wt residualYSWeights F-wt residualSWeights F)+
      (wt residualTotalWeights F-wt residualYSWeights F) = wt residualTotalWeights F
    omega
  let S := ofCarrier D L s F hDlow hDchar hF hrdegree hbox ht hy hr h3 hry hyt
    selected seeds hdegree hagreement hsolution hregular hno
  have hown : MovingFiberArithmeticBase6815.Own S := rfl
  have hL : MovingFiberCount6815.sourceLimit g < S.t := by
    change MovingFiberCount6815.sourceLimit g < wt residualTotalWeights F
    rw [← htotal]
    exact ha'.2.2.2
  exact MovingFiberCount6815.count_group S hI hown g hL

end Carrier
end
end ProximityPrize.SubmissionLower.MovingFiberCarrier6815
end MergedPart3
