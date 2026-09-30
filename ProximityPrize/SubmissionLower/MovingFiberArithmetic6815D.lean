import ProximityPrize.SubmissionLower.MovingFiberArithmetic6815C
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
