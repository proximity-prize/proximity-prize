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
def scale : ℕ := 360
def denominator : ℕ := 6506438400
def g0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    332748055147488*a +
    100118132498925*b +
    838316295662490
def identitySlack0 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    15704946161809601952*a +
    5026330723976030700*b +
    39585988310402433960
def helperSlack0 (a b c : ℕ) : ℕ :=
    73986948831715277760*a^3 +
    222495209146213865280*a^2*b +
    223029571797281897280*a^2*c +
    64765240157622501225684*a^2 +
    223029571797281897280*a*b^2 +
    446593506245631826560*a*b*c +
    144585065351634394312008*a*b +
    12747399004987483394376*a*c +
    568525645327875837936840*a +
    2033019207712507766364*b^2 +
    4023370379377690826328*b*c +
    389831723122809118966920*b +
    36656548569554282710344*c +
    1035389668114642388617620
def g1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3559828776363144*a +
    100118132498925*b +
    97755839865100*c +
    8172608363990250
def identitySlack1 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    176716969490905510176*a +
    5026330723976030700*b +
    4907734184587480400*c +
    405295944311692083000
def helperSlack1 (a b c : ℕ) : ℕ :=
    73746485638734663360*a^3 +
    222014282760252636480*a^2*b +
    222789108604301282880*a^2*c +
    64762429734952830758484*a^2 +
    222789108604301282880*a*b^2 +
    446353043052651212160*a*b*c +
    144581493462186951899208*a*b +
    12744981013685633455176*a*c +
    568514741631474271229640*a +
    2032257740934735820764*b^2 +
    4022608912599918880728*b*c +
    389825079460305403822920*b +
    36651492161898366627144*c +
    1035375405968779488592020
def g2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3559828776363144*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4395796893621135*b +
    331236187861840*c +
    13632419079716910
def identitySlack2 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    176716969490905510176*a +
    207002715165818880*b^2 +
    414005430331637760*b*c +
    218685912849725690340*b +
    15629044376600929760*c +
    676399262255679737640
def helperSlack2 (a b c : ℕ) : ℕ :=
    73452586180647245760*a^3 +
    221426483844077801280*a^2*b +
    222495209146213865280*a^2*c +
    64758112085977395216084*a^2 +
    222495209146213865280*a*b^2 +
    446059143594563794560*a*b*c +
    144576254037638424001608*a*b +
    12742304747034485723976*a*c +
    568494610583704338596040*a +
    2031335965361643465564*b^2 +
    4021687137026826525528*b*c +
    389814597131565903781320*b +
    36646099550853655116744*c +
    1035345988198996590976020
def conductor (a b c : ℕ) : ℕ :=
    334023088512960*a^3 +
    1002069265538880*a^2*b +
    1002069265538880*a^2*c +
    75615798006349524*a^2 +
    1002069265538880*a*b^2 +
    2004138531077760*a*b*c +
    151231596012699048*a*b +
    17705700460042056*a*c +
    731106248425023240*a +
    3932834605725564*b^2 +
    7865669211451128*b*c +
    448382671884682920*b +
    47804985226711944*c +
    1525501693844209620
def slope (a b : ℕ) : ℕ :=
    223563934448349929280*a^2 +
    447127868896699858560*a*b +
    12753009813503180162376*a +
    4025107057993661930328*b +
    36668538334000745494344
def intercept (a b : ℕ) : ℕ :=
    74521311482783309760*a^3 +
    223563934448349929280*a^2*b +
    64801490993750814979284*a^2 +
    223563934448349929280*a*b^2 +
    144623052866378679169608*a*b +
    568782532302227356445640*a +
    2034755886328478870364*b^2 +
    389929327286561064949320*b +
    1035834485235946521164820
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 12 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source23,source24,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80870*identityDegree f a b c ≤ 50204*graph cfg scale f a b c := by
  have he : 50204*graph cfg scale f a b c = scale*131073*80870*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50204*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50204
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50204) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50204)*50204 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
def scale : ℕ := 360
def denominator : ℕ := 6506438400
def g0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    332748055147488*a +
    100118132498925*b +
    838316295662490
def identitySlack0 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    15704946161809601952*a +
    5026330723976030700*b +
    39585988310402433960
def helperSlack0 (a b c : ℕ) : ℕ :=
    73960230699161876160*a^3 +
    222441772881107062080*a^2*b +
    223002853664728495680*a^2*c +
    64764923070931327838484*a^2 +
    223002853664728495680*a*b^2 +
    446566788113078424960*a*b*c +
    144584681599908507678408*a*b +
    12610584216866718549576*a*c +
    568524441400964664260040*a +
    2032952424226276103964*b^2 +
    4057459411080513491928*b*c +
    389831102350850689760520*b +
    36314680814091875475144*c +
    1035388234354571310990420
def g1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3559828776363144*a +
    100118132498925*b +
    99645673972160*c +
    8172608363990250
def identitySlack1 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    176716969490905510176*a +
    5026330723976030700*b +
    5002611416098320640*c +
    405295944311692083000
def helperSlack1 (a b c : ℕ) : ℕ :=
    73746485638734663360*a^3 +
    222014282760252636480*a^2*b +
    222789108604301282880*a^2*c +
    64762501113602976753684*a^2 +
    222789108604301282880*a*b^2 +
    446353043052651212160*a*b*c +
    144581573877177952619208*a*b +
    12608330987416255375176*a*c +
    568515313569405689146440*a +
    2032266658824072129564*b^2 +
    4056773645678309517528*b*c +
    389825341317468075930120*b +
    36309880455308185188744*c +
    1035376484927544423044820
def g2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3559828776363144*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4395796893621135*b +
    323676851433600*c +
    13632419079716910
def identitySlack2 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    176716969490905510176*a +
    207002715165818880*b^2 +
    414005430331637760*b*c +
    218685912849725690340*b +
    15249535450557568800*c +
    676399262255679737640
def helperSlack2 (a b c : ℕ) : ℕ :=
    73452586180647245760*a^3 +
    221426483844077801280*a^2*b +
    222495209146213865280*a^2*c +
    64758183464627541211284*a^2 +
    222495209146213865280*a*b^2 +
    446059143594563794560*a*b*c +
    144576334452629424721608*a*b +
    12605654720765107643976*a*c +
    568495182521635756512840*a +
    2031344883250979774364*b^2 +
    4055851870105217162328*b*c +
    389814858988728575888520*b +
    36304487844263473678344*c +
    1035347067157761525428820
def conductor (a b c : ℕ) : ℕ :=
    334023088512960*a^3 +
    1002069265538880*a^2*b +
    1002069265538880*a^2*c +
    75746094676607124*a^2 +
    1002069265538880*a*b^2 +
    2004138531077760*a*b*c +
    151492189353214248*a*b +
    17610939245309256*a*c +
    732409215127599240*a +
    3944679757567164*b^2 +
    7889359515134328*b*c +
    449211832513594920*b +
    47568082189879944*c +
    1528285304526985620
def slope (a b : ℕ) : ℕ :=
    223563934448349929280*a^2 +
    447127868896699858560*a*b +
    12616359787233802082376*a +
    4059271791072052567128*b +
    36326926627410564055944
def intercept (a b : ℕ) : ℕ :=
    74521311482783309760*a^3 +
    223563934448349929280*a^2*b +
    64801562372400960974484*a^2 +
    223563934448349929280*a*b^2 +
    144623133281369679889608*a*b +
    568783104240158774362440*a +
    2034764804217815179164*b^2 +
    389929589143723737056520*b +
    1035835564194711455617620
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 13 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source24,source25,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80870*identityDegree f a b c ≤ 50204*graph cfg scale f a b c := by
  have he : 50204*graph cfg scale f a b c = scale*131073*80870*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50204*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50204
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50204) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50204)*50204 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
def scale : ℕ := 360
def denominator : ℕ := 6506438400
def g0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    331614154683252*a +
    100118132498925*b +
    835739242932930
def identitySlack0 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    15648019822903097808*a +
    5026330723976030700*b +
    39456609955167603720
def helperSlack0 (a b c : ℕ) : ℕ :=
    73960230699161876160*a^3 +
    222441772881107062080*a^2*b +
    223002853664728495680*a^2*c +
    65523493774489841918676*a^2 +
    223002853664728495680*a*b^2 +
    446566788113078424960*a*b*c +
    145343243555200259821512*a*b +
    12590072914243498797384*a*c +
    574041451515751839276360*a +
    2032943513917836973788*b^2 +
    4057450496507819698776*b*c +
    391555215083908915137288*b +
    36268035541705373277384*c +
    1044009017742505903733268
def g1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3601783093539876*a +
    100118132498925*b +
    99645673972160*c +
    8267959314983970
def identitySlack1 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    178823244030446163504*a +
    5026330723976030700*b +
    5002611416098320640*c +
    410082943455380801880
def helperSlack1 (a b c : ℕ) : ℕ :=
    73746485638734663360*a^3 +
    222014282760252636480*a^2*b +
    222789108604301282880*a^2*c +
    65521071817161490833876*a^2 +
    222789108604301282880*a*b^2 +
    446353043052651212160*a*b*c +
    145340135832469704762312*a*b +
    12587819684793035622984*a*c +
    574032323684192864162760*a +
    2032257748515632999388*b^2 +
    4056764731105615724376*b*c +
    391549454050526301306888*b +
    36263235182921682990984*c +
    1043997268315479015787668
def g2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3601783093539876*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4395796893621135*b +
    323676851433600*c +
    13727770030710630
def identitySlack2 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    178823244030446163504*a +
    207002715165818880*b^2 +
    414005430331637760*b*c +
    218685912849725690340*b +
    15249535450557568800*c +
    681186261399368456520
def helperSlack2 (a b c : ℕ) : ℕ :=
    73479304313200647360*a^3 +
    221479920109184604480*a^2*b +
    222521927278767266880*a^2*c +
    65516759673627442584276*a^2 +
    222521927278767266880*a*b^2 +
    446085861727117196160*a*b*c +
    145334977614738132128712*a*b +
    12585352710214196992584*a*c +
    574011003192188972853960*a +
    2031411674318108615388*b^2 +
    4055918656908091340376*b*c +
    391538801211183089332488*b +
    36258221078856733701384*c +
    1043965105456351834296468
def conductor (a b c : ℕ) : ℕ :=
    334023088512960*a^3 +
    1002069265538880*a^2*b +
    1002069265538880*a^2*c +
    75903872099137236*a^2 +
    1002069265538880*a*b^2 +
    2004138531077760*a*b*c +
    151807744198274472*a*b +
    17602410735983304*a*c +
    733986989352900360*a +
    3940415502904188*b^2 +
    7880831005808376*b*c +
    450141440030123688*b +
    47525439643250184*c +
    1531581573381466068
def slope (a b : ℕ) : ℕ :=
    223563934448349929280*a^2 +
    447127868896699858560*a*b +
    12595848484610582330184*a +
    4059262876499358773976*b +
    36280281355024061858184
def intercept (a b : ℕ) : ℕ :=
    74521311482783309760*a^3 +
    223563934448349929280*a^2*b +
    65560133075959475054676*a^2 +
    223563934448349929280*a*b^2 +
    145381695236661432032712*a*b +
    574300114354945949378760*a +
    2034755893909376048988*b^2 +
    391653701876781962433288*b +
    1044456347582646048360468
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 14 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source25,source26,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80870*identityDegree f a b c ≤ 50204*graph cfg scale f a b c := by
  have he : 50204*graph cfg scale f a b c = scale*131073*80870*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50204*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50204
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50204) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50204)*50204 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
def scale : ℕ := 360
def denominator : ℕ := 6506438400
def g0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    331614154683252*a +
    100118132498925*b +
    835739242932930
def identitySlack0 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    15648019822903097808*a +
    5026330723976030700*b +
    39456609955167603720
def helperSlack0 (a b c : ℕ) : ℕ :=
    73933512566608474560*a^3 +
    222388336616000258880*a^2*b +
    222976135532175094080*a^2*c +
    65523176782559883264276*a^2 +
    222976135532175094080*a*b^2 +
    446540069980525023360*a*b*c +
    145342859992996802653512*a*b +
    12589881434259558630984*a*c +
    574040248536452812927560*a +
    2032876718586453469788*b^2 +
    4057383701176436194776*b*c +
    391554594833137166961288*b +
    36267726056585027738184*c +
    1044007585925039728128468
def g1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3601783093539876*a +
    100118132498925*b +
    99645673972160*c +
    8267959314983970
def identitySlack1 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    178823244030446163504*a +
    5026330723976030700*b +
    5002611416098320640*c +
    410082943455380801880
def helperSlack1 (a b c : ℕ) : ℕ :=
    73746485638734663360*a^3 +
    222014282760252636480*a^2*b +
    222789108604301282880*a^2*c +
    65521241257058880701076*a^2 +
    222789108604301282880*a*b^2 +
    446353043052651212160*a*b*c +
    145340305497424979619912*a*b +
    12587819684793035622984*a*c +
    574033637350100631017160*a +
    2032257748515632999388*b^2 +
    4056764731105615724376*b*c +
    391549920741682249660488*b +
    36263235182921682990984*c +
    1043999599746706055107668
def g2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3601783093539876*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4395796893621135*b +
    323676851433600*c +
    13727770030710630
def identitySlack2 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    178823244030446163504*a +
    207002715165818880*b^2 +
    414005430331637760*b*c +
    218685912849725690340*b +
    15249535450557568800*c +
    681186261399368456520
def helperSlack2 (a b c : ℕ) : ℕ :=
    73479304313200647360*a^3 +
    221479920109184604480*a^2*b +
    222521927278767266880*a^2*c +
    65516929113524832451476*a^2 +
    222521927278767266880*a*b^2 +
    446085861727117196160*a*b*c +
    145335147279693406986312*a*b +
    12585352710214196992584*a*c +
    574012316858096739708360*a +
    2031411674318108615388*b^2 +
    4055918656908091340376*b*c +
    391539267902339037686088*b +
    36258221078856733701384*c +
    1043967436887578873616468
def conductor (a b c : ℕ) : ℕ :=
    334023088512960*a^3 +
    1002069265538880*a^2*b +
    1002069265538880*a^2*c +
    76128929984127636*a^2 +
    1002069265538880*a*b^2 +
    2004138531077760*a*b*c +
    152257859968255272*a*b +
    17602410735983304*a*c +
    736237568202804360*a +
    3940415502904188*b^2 +
    7880831005808376*b*c +
    451491787340066088*b +
    47525439643250184*c +
    1536307788966264468
def slope (a b : ℕ) : ℕ :=
    223563934448349929280*a^2 +
    447127868896699858560*a*b +
    12595848484610582330184*a +
    4059262876499358773976*b +
    36280281355024061858184
def intercept (a b : ℕ) : ℕ :=
    74521311482783309760*a^3 +
    223563934448349929280*a^2*b +
    65560302515856864921876*a^2 +
    223563934448349929280*a*b^2 +
    145381864901616706890312*a*b +
    574301428020853716233160*a +
    2034755893909376048988*b^2 +
    391654168567937910786888*b +
    1044458679013873087680468
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 15 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source21,source26,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80870*identityDegree f a b c ≤ 50204*graph cfg scale f a b c := by
  have he : 50204*graph cfg scale f a b c = scale*131073*80870*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50204*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50204
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50204) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50204)*50204 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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


