import ProximityPrize.SubmissionLower.MovingFiberArithmetic6815D
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
    157315841655398830*b +
    1228313421222158380
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099995305746062*b +
    27799225870370845752*c +
    661960166432127738678
def gLo1 (b c : ℕ) : ℕ :=
    3135405621545*b +
    3135405621545*c +
    222013137897940
def identitySlackLo1 (b c : ℕ) : ℕ :=
    157315841655398830*b +
    157315841655398830*c +
    11014198644684792560
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099995305746062*b +
    27799225870370845752*c +
    661960166432127738678
def gLo2 (b c : ℕ) : ℕ :=
    103080787968*b^2 +
    206161575936*b*c +
    96372947231681*b +
    9852907357087*c +
    340507472465668
def identitySlackLo2 (b c : ℕ) : ℕ :=
    5171975455506432*b^2 +
    10343950911012864*b*c +
    4785380839919782894*b +
    469342066493193338*c +
    16884480074693605232
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1555253576188380108*b^2 +
    3110746502314217772*b*c +
    233674099995305746062*b +
    27799225870370845752*c +
    661960166432127738678
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
    5171975455506432*a^2 +
    10343950911012864*a*b +
    487443980587465850*a +
    165073804838658478*b +
    1707999399167925414
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452410897763864*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440214734408*a*b +
    9712390124912171688*a*c +
    459106978471847710506*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307043675031122*b +
    37302382819777725828*c +
    1077166458531862994988
def gHi1 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    96579108807617*a +
    3290026803497*b +
    3290026803497*c +
    318437624737173
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    5171975455506432*a^2 +
    10343950911012864*a*b +
    10343950911012864*a*c +
    4795724790830795758*a +
    165073804838658478*b +
    165073804838658478*c +
    15802165432873889502
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452410897763864*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440214734408*a*b +
    9712390124912171688*a*c +
    459106978471847710506*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307043675031122*b +
    37302382819777725828*c +
    1077166458531862994988
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
    5171975455506432*a^2 +
    10343950911012864*a*b +
    10343950911012864*a*c +
    4795724790830795758*a +
    5171975455506432*b^2 +
    10343950911012864*b*c +
    4795724790830795758*b +
    479686017404206202*c +
    21675032890068894558
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    46314528136772580*a^3 +
    139177368070160004*a^2*b +
    139411151730002268*a^2*c +
    43900452410897763864*a^2 +
    139411151730002268*a*b^2 +
    279056087119846800*a*b*c +
    87791206440214734408*a*b +
    9712390124912171688*a*c +
    459106978471847710506*a +
    1671390838368603432*b^2 +
    3343254810334506684*b*c +
    321256307043675031122*b +
    37302382819777725828*c +
    1077166458531862994988
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
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
    230586223929788570*b +
    1777093029167181540
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160084648492338*b +
    67671072422978742294*c +
    1926796317162342193788
def gLo1 (b c : ℕ) : ℕ :=
    4595731333555*b +
    4595731333555*c +
    386901582053470
def identitySlackLo1 (b c : ℕ) : ℕ :=
    230586223929788570*b +
    230586223929788570*c +
    19203919084273388780
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160084648492338*b +
    67671072422978742294*c +
    1926796317162342193788
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    168401395793532*b +
    14405689214281*c +
    595095629789680
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8619959092510720*b^2 +
    17239918185021440*b*c +
    8365979275073708568*b +
    681094871901851894*c +
    29524758381069369320
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3845658939034219770*b^2 +
    7692361555121306790*b*c +
    678480160084648492338*b +
    67671072422978742294*c +
    1926796317162342193788
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
    8619959092510720*a^2 +
    17239918185021440*a*b +
    711264728725639414*a +
    243516162568554650*b +
    2475427753489989594
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140683801440438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264198275342976*a*b +
    23943378800113756068*a*c +
    1337265026559225397926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521591398449934*b +
    91033574432984436882*c +
    3136239227854089945036
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    168744998420092*a +
    4853433303475*b +
    4853433303475*c +
    555388877192922
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8619959092510720*a^2 +
    17239918185021440*a*b +
    17239918185021440*a*c +
    8383219193258730008*a +
    243516162568554650*b +
    243516162568554650*c +
    27574208273129287428
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140683801440438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264198275342976*a*b +
    23943378800113756068*a*c +
    1337265026559225397926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521591398449934*b +
    91033574432984436882*c +
    3136239227854089945036
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
    8619959092510720*a^2 +
    17239918185021440*a*b +
    17239918185021440*a*c +
    8383219193258730008*a +
    8619959092510720*b^2 +
    17239918185021440*b*c +
    8383219193258730008*b +
    698334790086873334*c +
    37899357615235588608
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    127821140683801440438*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    255594264198275342976*a*b +
    23943378800113756068*a*c +
    1337265026559225397926*a +
    4167935969905980450*b^2 +
    8337889715447504250*b*c +
    933494521591398449934*b +
    91033574432984436882*c +
    3136239227854089945036
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
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
    221104170281025726*b +
    1743474609979002740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386795577736642*b +
    66455555295435346704*c +
    2088448379710254628512
def gLo1 (b c : ℕ) : ℕ :=
    4406747922849*b +
    4406747922849*c +
    418874213305030
def identitySlackLo1 (b c : ℕ) : ℕ :=
    221104170281025726*b +
    221104170281025726*c +
    20808113884689160220
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386795577736642*b +
    66455555295435346704*c +
    2088448379710254628512
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    182575151596482*b +
    14216705803575*c +
    645348379004680
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8619959092510720*b^2 +
    17239918185021440*b*c +
    9077133298730921868*b +
    671612818253089050*c +
    32046139820182779320
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3703427956731672666*b^2 +
    7407899590516212582*b*c +
    734273386795577736642*b +
    66455555295435346704*c +
    2088448379710254628512
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
    8619959092510720*a^2 +
    17239918185021440*a*b +
    701782675076876570*a +
    234034108919791806*b +
    2432327280653047950
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102921171883238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550108336818576*a*b +
    23658885911744132460*a*c +
    1449802304631815149026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034212389169838*b +
    89533564417071417684*c +
    3399756606237221688060
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    182918754223042*a +
    4664449892769*b +
    4664449892769*c +
    601535264247432
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8619959092510720*a^2 +
    17239918185021440*a*b +
    17239918185021440*a*c +
    9094373216915943308*a +
    234034108919791806*b +
    234034108919791806*c +
    29889557097202272168
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102921171883238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550108336818576*a*b +
    23658885911744132460*a*c +
    1449802304631815149026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034212389169838*b +
    89533564417071417684*c +
    3399756606237221688060
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
    8619959092510720*a^2 +
    17239918185021440*a*b +
    17239918185021440*a*c +
    9094373216915943308*a +
    8619959092510720*b^2 +
    17239918185021440*b*c +
    9094373216915943308*b +
    688852736438110490*c +
    41131893078006211908
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128326175633412960*a^3 +
    385952625482914980*a^2*b +
    386926724065591080*a^2*c +
    138493102921171883238*a^2 +
    386926724065591080*a*b^2 +
    774827546713858260*a*b*c +
    276933550108336818576*a*b +
    23658885911744132460*a*c +
    1449802304631815149026*a +
    4025704987603433346*b^2 +
    8053427750842410042*b*c +
    1010627034212389169838*b +
    89533564417071417684*c +
    3399756606237221688060
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
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
    303856606204178310*b +
    2315097550141126080
def helperSlackLo0 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792374216671000*b +
    124092480563104145490*c +
    3865958020349682371682
def gLo1 (b c : ℕ) : ℕ :=
    6056057045565*b +
    6056057045565*c +
    553937570150300
def identitySlackLo1 (b c : ℕ) : ℕ :=
    303856606204178310*b +
    303856606204178310*c +
    27501390393572771200
def helperSlackLo1 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792374216671000*b +
    124092480563104145490*c +
    3865958020349682371682
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    241374761408913*b +
    18863979366122*c +
    853033970394692
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12067942729515008*b^2 +
    24135885459030016*b*c +
    11993987978471448462*b +
    888106650486129028*c +
    42333128783386027408
def helperSlackLo2 (b c : ℕ) : ℕ :=
    7138723507332488010*b^2 +
    14280007811605655634*b*c +
    1359830792374216671000*b +
    124092480563104145490*c +
    3865958020349682371682
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    930344450039431556*a +
    321958520298450822*b +
    3227339994016593732
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131839194863646*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259218966239048*a*b +
    44179544752331505780*a*c +
    2683853783752426198524*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534799757511412*b +
    167134053793581908862*c +
    6293324214910518123888
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    241855805086097*a +
    6416839803453*b +
    6416839803453*c +
    795432590643501
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    12018123863930478478*a +
    321958520298450822*b +
    321958520298450822*c +
    39501412251339285774
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131839194863646*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259218966239048*a*b +
    44179544752331505780*a*c +
    2683853783752426198524*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534799757511412*b +
    167134053793581908862*c +
    6293324214910518123888
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
    12067942729515008*a^2 +
    24135885459030016*a*b +
    24135885459030016*a*c +
    12018123863930478478*a +
    12067942729515008*b^2 +
    24135885459030016*b*c +
    12018123863930478478*b +
    912242535945159044*c +
    54339184704586990878
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    250973311851270960*a^3 +
    755374663982156652*a^2*b +
    757829392410500424*a^2*c +
    256485131839194863646*a^2 +
    757829392410500424*a*b^2 +
    1518113513249344620*a*b*c +
    512833259218966239048*a*b +
    44179544752331505780*a*c +
    2683853783752426198524*a +
    7769839501083080850*b^2 +
    15544694527535185086*b*c +
    1871528534799757511412*b +
    167134053793581908862*c +
    6293324214910518123888
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
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G19
