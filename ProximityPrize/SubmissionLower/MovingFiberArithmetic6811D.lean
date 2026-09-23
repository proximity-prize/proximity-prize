import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811C

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G12
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source23,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6505142400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    38128559209260616020
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883601983099283882354*b^2 +
    3724544434404724828308*b*c +
    396938096474435597604060*b +
    34935606076776518416284*c +
    1054656185952180073190310
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    89509376827660*c +
    8311254044951490
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    4492833660487566040*c +
    412172781053492817060
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882840516321511936754*b^2 +
    3723782967626952882708*b*c +
    396932334512810778760860*b +
    34930549669120602333084*c +
    1054646332318628939923110
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4487539856605575*b +
    314743261786960*c +
    13898888162149110
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223246653770939322750*b +
    14797762386374215840*c +
    689637097611976139340
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881918740748419581554*b^2 +
    3722861192053860527508*b*c +
    396922023628443293008860*b +
    34925157058075890822684*c +
    1054617771774879427247910
def conductorLo (b c : ℕ) : ℕ :=
    3932051234957154*b^2 +
    7864102469914308*b*c +
    460508015863981260*b +
    47795463080025084*c +
    1567949129677130310
def slopeLo (b : ℕ) : ℕ :=
    3726281113020695932308*b +
    34947595841222981200284
def interceptLo (b : ℕ) : ℕ :=
    1885338661715254986354*b^2 +
    397038345727545696424860*b +
    1055114228509677558748710
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    15598014242887242432*a +
    4921848801225725610*b +
    53416129648905198612
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73972105131714723360*a^3 +
    222450678046212202080*a^2*b +
    222985040697280234080*a^2*c +
    66121034684751226387494*a^2 +
    222985040697280234080*a*b^2 +
    446504444045628500160*a*b*c +
    147805728515445092141628*a*b +
    12706540433375307282396*a*c +
    710984902948864401910248*a +
    2069333956883450414034*b^2 +
    4096542744624125923668*b*c +
    544409614542667120001208*b +
    47307401700287187922200*c +
    1699519519050742703161224
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3631470690779124*a +
    98056516739565*b +
    95694224105740*c +
    11936539856995254
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    180277118061446441256*a +
    4921848801225725610*b +
    4803275884763513560*c +
    592139455311696598476
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73731641938734108960*a^3 +
    221969751660250973280*a^2*b +
    222744577504299619680*a^2*c +
    66117823490808864624294*a^2 +
    222744577504299619680*a*b^2 +
    446263980852647885760*a*b*c +
    147801515391531977818428*a*b +
    12703641515687496114396*a*c +
    710970783049206297641448*a +
    2068332026912697854034*b^2 +
    4095540814653373363668*b*c +
    544400120383515148063608*b +
    47299686838136441285400*c +
    1699498516248282846774024
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3631470690779124*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4495786319643015*b +
    322989724824400*c +
    17526235621409514
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    180277118061446441256*a +
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223660576736640586110*b +
    15211685352075479200*c +
    869707254190571948916
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73437742480646691360*a^3 +
    221381952744076138080*a^2*b +
    222450678046212202080*a^2*c +
    66112686486643092211494*a^2 +
    222450678046212202080*a*b^2 +
    445970081394560468160*a*b*c +
    147795162712335025632828*a*b +
    12700377450120173547996*a*c +
    710941742853161828134248*a +
    2067116351881518081234*b^2 +
    4094325139622193590868*b*c +
    544384044618866884961208*b +
    47291324060982494626200*c +
    1699445758613196549586824
def conductorHi (a b c : ℕ) : ℕ :=
    333956555350560*a^3 +
    1001869666051680*a^2*b +
    1001869666051680*a^2*c +
    78638381984591334*a^2 +
    1001869666051680*a*b^2 +
    2003739332103360*a*b*c +
    157276763969182668*a*b +
    19705913041197276*a*c +
    907593275837235528*a +
    4933920901008834*b^2 +
    9867841802017668*b*c +
    616782910167112248*b +
    66499506455170680*c +
    2397237980085125064
def slopeHi (a b : ℕ) : ℕ :=
    223519403348348266080*a^2 +
    447038806696696532160*a*b +
    12713219967193140114396*a +
    4098813785891165059668*b +
    47325536635900415506200
def interceptHi (a b : ℕ) : ℕ :=
    74506467782782755360*a^3 +
    223519403348348266080*a^2*b +
    66159850460014422854694*a^2 +
    223519403348348266080*a*b^2 +
    147846815331975327744828*a*b +
    711325272727523184790248*a +
    2071604998150489550034*b^2 +
    544549881887005318361208*b +
    1700279649974286843164424
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
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G12

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G13
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source25,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6505142400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    38128559209260616020
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883535199610692815954*b^2 +
    3758626662700043269908*b*c +
    396937476342021582228060*b +
    34593806355389153421084*c +
    1054654754430716940441510
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8311254044951490
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    4587691993657335680*c +
    412172781053492817060
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882849434208488841554*b^2 +
    3757940897297839295508*b*c +
    396932817433872893685660*b +
    34589005996605463134684*c +
    1054648515638831956271910
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4487539856605575*b +
    307183925358720*c +
    13898888162149110
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223246653770939322750*b +
    14418329053695137280*c +
    689637097611976139340
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881927658635396486354*b^2 +
    3757019121724746940308*b*c +
    396922506549505407933660*b +
    34583613385560751624284*c +
    1054619955095082443596710
def conductorLo (b c : ℕ) : ℕ :=
    3943894027394754*b^2 +
    7887788054789508*b*c +
    461976522126243660*b +
    47558607231273084*c +
    1572970473670672710
def slopeLo (b : ℕ) : ℕ :=
    3760439042691582345108*b +
    34606052168707842001884
def interceptLo (b : ℕ) : ℕ :=
    1885347579602231891154*b^2 +
    397038828648607811349660*b +
    1055116411829880575097510
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    15598014242887242432*a +
    4921848801225725610*b +
    53416129648905198612
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73945386999161321760*a^3 +
    222397241781105398880*a^2*b +
    222958322564726832480*a^2*c +
    66120637550301083481894*a^2 +
    222958322564726832480*a*b^2 +
    446477725913075098560*a*b*c +
    147805238104386861082428*a*b +
    12569699422619452530396*a*c +
    710982985973598972915048*a +
    2069240455262305946034*b^2 +
    4130598254786890963668*b*c +
    544408557435459980369208*b +
    46828787686276521576600*c +
    1699516540970331730921224
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3631470690779124*a +
    98056516739565*b +
    97584058212800*c +
    11936539856995254
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    180277118061446441256*a +
    4921848801225725610*b +
    4898134217933283200*c +
    592139455311696598476
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73731641938734108960*a^3 +
    221969751660250973280*a^2*b +
    222744577504299619680*a^2*c +
    66117975130415849318694*a^2 +
    222744577504299619680*a*b^2 +
    446263980852647885760*a*b*c +
    147801676174038995732028*a*b +
    12567018703048134930396*a*c +
    710972280528797488313448*a +
    2068340944799674758834*b^2 +
    4129698744324259776468*b*c +
    544400764087084280902008*b +
    46821520352981940903000*c +
    1699502045408470069100424
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3631470690779124*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4495786319643015*b +
    315430388396160*c +
    17526235621409514
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    180277118061446441256*a +
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223660576736640586110*b +
    14832252019396400640*c +
    869707254190571948916
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73437742480646691360*a^3 +
    221381952744076138080*a^2*b +
    222450678046212202080*a^2*c +
    66112838126250076905894*a^2 +
    222450678046212202080*a*b^2 +
    445970081394560468160*a*b*c +
    147795323494842043546428*a*b +
    12563754637480812363996*a*c +
    710943240332753018806248*a +
    2067125269768494986034*b^2 +
    4128483069293080003668*b*c +
    544384688322436017799608*b +
    46813157575827994243800*c +
    1699449287773383771913224
def conductorHi (a b c : ℕ) : ℕ :=
    333956555350560*a^3 +
    1001869666051680*a^2*b +
    1001869666051680*a^2*c +
    78875237833343334*a^2 +
    1001869666051680*a*b^2 +
    2003739332103360*a*b*c +
    157750475666686668*a*b +
    19611170701696476*a*c +
    910435546022259528*a +
    4945763693446434*b^2 +
    9891527386892868*b*c +
    618725128126878648*b +
    66167908266917880*c +
    2404864738414939464
def slopeHi (a b : ℕ) : ℕ :=
    223519403348348266080*a^2 +
    447038806696696532160*a*b +
    12576597154553778930396*a +
    4132971715562051472468*b +
    46847370150745915123800
def interceptHi (a b : ℕ) : ℕ :=
    74506467782782755360*a^3 +
    223519403348348266080*a^2*b +
    66160002099621407549094*a^2 +
    223519403348348266080*a*b^2 +
    147846976114482345658428*a*b +
    711326770207114375462248*a +
    2071613916037466454834*b^2 +
    544550525590574451199608*b +
    1700283179134474065490824
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
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G13

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G14
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source25,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6505142400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    37999206624553081380
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883526289303103071218*b^2 +
    3758617748129048247636*b*c +
    398754428706904123123740*b +
    34547170360400971493724*c +
    1063739735901522261620550
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8411759101404330
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    4587691993657335680*c +
    417217531857086668020
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882840523900899096818*b^2 +
    3757931982726844273236*b*c +
    398749769798755434581340*b +
    34542370001617281207324*c +
    1063733497109637277450950
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4487539856605575*b +
    307183925358720*c +
    13999393218601950
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223246653770939322750*b +
    14418329053695137280*c +
    694681848415569990300
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881994449703374712818*b^2 +
    3757085908529319889236*b*c +
    398739239420302685750940*b +
    34537355897552331917724*c +
    1063701946559033802807750
def conductorLo (b c : ℕ) : ℕ :=
    3939630622117218*b^2 +
    7879261244234436*b*c +
    462957105340076940*b +
    47515973178497724*c +
    1576445148971864550
def slopeLo (b : ℕ) : ℕ :=
    3760430128120587322836*b +
    34559416173719660074524
def interceptLo (b : ℕ) : ℕ :=
    1885338669294642146418*b^2 +
    398855781013490352245340*b +
    1064201393300685896276550
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    15541099242985380648*a +
    4921848801225725610*b +
    53229862064295802188
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73945386999161321760*a^3 +
    222397241781105398880*a^2*b +
    222958322564726832480*a^2*c +
    66920053838830854039558*a^2 +
    222958322564726832480*a*b^2 +
    446477725913075098560*a*b*c +
    148604645653145252996796*a*b +
    12549192202039602798684*a*c +
    718395896213701236335016*a +
    2069231544954716201298*b^2 +
    4130589340215895941396*b*c +
    547024917349100913179256*b +
    46761644470708489917528*c +
    1715215016392709544962568
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3675692808884328*a +
    98056516739565*b +
    97584058212800*c +
    12081267031553298
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    182496803057619050832*a +
    4921848801225725610*b +
    4898134217933283200*c +
    599403891111463059012
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73731641938734108960*a^3 +
    221969751660250973280*a^2*b +
    222744577504299619680*a^2*c +
    66917391418945619876358*a^2 +
    222744577504299619680*a*b^2 +
    446263980852647885760*a*b*c +
    148601083722797387646396*a*b +
    12546511482468285198684*a*c +
    718385190768899751733416*a +
    2068332034492085014098*b^2 +
    4129689829753264754196*b*c +
    547017124000725213712056*b +
    46754377137413909243928*c +
    1715200520830847883141768
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3675692808884328*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4495786319643015*b +
    315430388396160*c +
    17670962795967558
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    182496803057619050832*a +
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223660576736640586110*b +
    14832252019396400640*c +
    876971689990338409452
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73464460613200092960*a^3 +
    221435389009182941280*a^2*b +
    222477396178765603680*a^2*c +
    66912322262451013834758*a^2 +
    222477396178765603680*a*b^2 +
    445996799527113869760*a*b*c +
    148594901310779723204796*a*b +
    12543510145238378536284*a*c +
    718354878625211065189416*a +
    2067218778969026614098*b^2 +
    4128576574230206354196*b*c +
    547000945572905868472056*b +
    46746628877444587307928*c +
    1715143460111724793980168
def conductorHi (a b c : ℕ) : ℕ :=
    333956555350560*a^3 +
    1001869666051680*a^2*b +
    1001869666051680*a^2*c +
    79041510639167238*a^2 +
    1001869666051680*a*b^2 +
    2003739332103360*a*b*c +
    158083021278334476*a*b +
    19602643891141404*a*c +
    912430819692146376*a +
    4941500288168898*b^2 +
    9883000576337796*b*c +
    620038256952359736*b +
    66116747403587448*c +
    2410168414580194248
def slopeHi (a b : ℕ) : ℕ :=
    223519403348348266080*a^2 +
    447038806696696532160*a*b +
    12556089933973929198684*a +
    4132962800991056450196*b +
    46780226935177883464728
def interceptHi (a b : ℕ) : ℕ :=
    74506467782782755360*a^3 +
    223519403348348266080*a^2*b +
    66959418388151178106758*a^2 +
    223519403348348266080*a*b^2 +
    148646383663240737572796*a*b +
    718739680447216638882216*a +
    2071605005729876710098*b^2 +
    547166885504215384009656*b +
    1715981654556851879532168
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
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G14

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G15
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source21,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6505142400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    37999206624553081380
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883459493971719567218*b^2 +
    3758550952797664743636*b*c +
    398753808598175692622940*b +
    34546860875280625954524*c +
    1063738304581386600310950
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8411759101404330
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    4587691993657335680*c +
    417217531857086668020
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882840523900899096818*b^2 +
    3757931982726844273236*b*c +
    398750285614998934699740*b +
    34542370001617281207324*c +
    1063736073953637192166950
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4487539856605575*b +
    307183925358720*c +
    13999393218601950
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223246653770939322750*b +
    14418329053695137280*c +
    694681848415569990300
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881994449703374712818*b^2 +
    3757085908529319889236*b*c +
    398739755236546185869340*b +
    34537355897552331917724*c +
    1063704523403033717523750
def conductorLo (b c : ℕ) : ℕ :=
    3939630622117218*b^2 +
    7879261244234436*b*c +
    464449297187214540*b +
    47515973178497724*c +
    1581667820436846150
def slopeLo (b : ℕ) : ℕ :=
    3760430128120587322836*b +
    34559416173719660074524
def interceptLo (b : ℕ) : ℕ :=
    1885338669294642146418*b^2 +
    398856296829733852363740*b +
    1064203970144685810992550
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    15541099242985380648*a +
    4921848801225725610*b +
    53229862064295802188
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73918668866607920160*a^3 +
    222343805515998595680*a^2*b +
    222931604432173430880*a^2*c +
    66919656716223503571558*a^2 +
    222931604432173430880*a*b^2 +
    446451007780521696960*a*b*c +
    148604155265772606812796*a*b +
    12548947285790555829084*a*c +
    718393979380549316591016*a +
    2069138031490779295698*b^2 +
    4130495826751959035796*b*c +
    547023860289264943297656*b +
    46761116787471650810328*c +
    1715212038643896760975368
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3675692808884328*a +
    98056516739565*b +
    97584058212800*c +
    12081267031553298
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    182496803057619050832*a +
    4921848801225725610*b +
    4898134217933283200*c +
    599403891111463059012
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73731641938734108960*a^3 +
    221969751660250973280*a^2*b +
    222744577504299619680*a^2*c +
    66917578694572134877158*a^2 +
    222744577504299619680*a*b^2 +
    446263980852647885760*a*b*c +
    148601271247122543836796*a*b +
    12546511482468285198684*a*c +
    718387017266186943944616*a +
    2068332034492085014098*b^2 +
    4129689829753264754196*b*c +
    547017827341293870020856*b +
    46754377137413909243928*c +
    1715204736896508475068168
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3675692808884328*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4495786319643015*b +
    315430388396160*c +
    17670962795967558
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    182496803057619050832*a +
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223660576736640586110*b +
    14832252019396400640*c +
    876971689990338409452
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73464460613200092960*a^3 +
    221435389009182941280*a^2*b +
    222477396178765603680*a^2*c +
    66912509538077528835558*a^2 +
    222477396178765603680*a*b^2 +
    445996799527113869760*a*b*c +
    148595088835104879395196*a*b +
    12543510145238378536284*a*c +
    718356705122498257400616*a +
    2067218778969026614098*b^2 +
    4128576574230206354196*b*c +
    547001648913474524780856*b +
    46746628877444587307928*c +
    1715147676177385385906568
def conductorHi (a b c : ℕ) : ℕ :=
    333956555350560*a^3 +
    1001869666051680*a^2*b +
    1001869666051680*a^2*c +
    79290209280356838*a^2 +
    1001869666051680*a*b^2 +
    2003739332103360*a*b*c +
    158580418560713676*a*b +
    19602643891141404*a*c +
    915415203386421576*a +
    4941500288168898*b^2 +
    9883000576337796*b*c +
    622027846081876536*b +
    66116747403587448*c +
    2418126771098261448
def slopeHi (a b : ℕ) : ℕ :=
    223519403348348266080*a^2 +
    447038806696696532160*a*b +
    12556089933973929198684*a +
    4132962800991056450196*b +
    46780226935177883464728
def interceptHi (a b : ℕ) : ℕ :=
    74506467782782755360*a^3 +
    223519403348348266080*a^2*b +
    66959605663777693107558*a^2 +
    223519403348348266080*a*b^2 +
    148646571187565893763196*a*b +
    718741506944503831093416*a +
    2071605005729876710098*b^2 +
    547167588844784040318456*b +
    1715985870622512471458568
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
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G15

