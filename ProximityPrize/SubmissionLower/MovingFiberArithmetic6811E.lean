import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811D

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G16
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source27,source27,source27]
def scale : ℕ := 9
def denominator : ℕ := 4066524
def g0 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    10265230508959*a +
    3341567197481*b +
    26449190324624
def identitySlack0 (a b c : ℕ) : ℕ :=
    5175067879145472*a^2 +
    10350135758290944*a*b +
    490347202501405496*a +
    167760039582336124*b +
    1265334076131492946
def helperSlack0 (a b c : ℕ) : ℕ :=
    46342360268033760*a^3 +
    139260864463943544*a^2*b +
    139494648123785808*a^2*c +
    41811514961405867748*a^2 +
    139494648123785808*a*b^2 +
    279223079907413880*a*b*c +
    83613409471206112104*a*b +
    9741949947206401104*a*c +
    354716792669333653020*a +
    1649334857162832684*b^2 +
    3298909064263122924*b*c +
    223643139666616469070*b +
    28887086828274233634*c +
    632287101497766409116
def g1 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    92000555639304*a +
    3341567197481*b +
    3341567197481*c +
    212211741247074
def identitySlack1 (a b c : ℕ) : ℕ :=
    5175067879145472*a^2 +
    10350135758290944*a*b +
    10350135758290944*a*c +
    4568779035374873736*a +
    167760039582336124*b +
    167760039582336124*c +
    10528836107716242396
def helperSlack1 (a b c : ℕ) : ℕ :=
    46342360268033760*a^3 +
    139260864463943544*a^2*b +
    139494648123785808*a^2*c +
    41811514961405867748*a^2 +
    139494648123785808*a*b^2 +
    279223079907413880*a*b*c +
    83613409471206112104*a*b +
    9741949947206401104*a*c +
    354716792669333653020*a +
    1649334857162832684*b^2 +
    3298909064263122924*b*c +
    223643139666616469070*b +
    28887086828274233634*c +
    632287101497766409116
def g2 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    92000555639304*a +
    103080787968*b^2 +
    206161575936*b*c +
    92000555639304*b +
    10265230508959*c +
    324864684230688
def identitySlack2 (a b c : ℕ) : ℕ :=
    5175067879145472*a^2 +
    10350135758290944*a*b +
    10350135758290944*a*c +
    4568779035374873736*a +
    5175067879145472*b^2 +
    10350135758290944*b*c +
    4568779035374873736*b +
    490347202501405496*c +
    16109438976556760052
def helperSlack2 (a b c : ℕ) : ℕ :=
    46342360268033760*a^3 +
    139260864463943544*a^2*b +
    139494648123785808*a^2*c +
    41811514961405867748*a^2 +
    139494648123785808*a*b^2 +
    279223079907413880*a*b*c +
    83613409471206112104*a*b +
    9741949947206401104*a*c +
    354716792669333653020*a +
    1649334857162832684*b^2 +
    3298909064263122924*b*c +
    223643139666616469070*b +
    28887086828274233634*c +
    632287101497766409116
def conductor (a b c : ℕ) : ℕ :=
    533015566776*a^3 +
    1599046700328*a^2*b +
    1599046700328*a^2*c +
    92747335593528*a^2 +
    1599046700328*a*b^2 +
    3198093400656*a*b*c +
    185494671187056*a*b +
    31803826042296*a*c +
    887497188427080*a +
    7018122337380*b^2 +
    14036244674760*b*c +
    550976522203800*b +
    89903986769520*c +
    1851040894188024
def slope (a b : ℕ) : ℕ :=
    139728431783628072*a^2 +
    279456863567256144*a*b +
    9744343446878250228*a +
    3299666078018802636*b +
    28892157708254072859
def intercept (a b : ℕ) : ℕ :=
    46576143927876024*a^3 +
    139728431783628072*a^2*b +
    41820368985205398504*a^2 +
    139728431783628072*a*b^2 +
    83623020508761322572*a*b +
    354774876520923414864*a +
    1650091870918512396*b^2 +
    223666555424292907245*b +
    632385337847826982338
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 16 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source27,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source27,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source27,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source27,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source27,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G16

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G17
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source28,source28,source28]
def scale : ℕ := 15
def denominator : ℕ := 11295900
def g0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    15092894467401*a +
    4939333960115*b +
    38698797239800
def identitySlack0 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    716042957224112904*a +
    247974322133613460*b +
    1838632625083701950
def helperSlack0 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    120289743931736482266*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    240532800424722506832*a*b +
    24024328103842355868*a*c +
    1020760138552637335710*a +
    4106712350500215270*b^2 +
    8214468378053297790*b*c +
    641499294715168271226*b +
    70687197603919805424*c +
    1818111777843119626536
def g1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    158814778309314*a +
    4939333960115*b +
    4939333960115*c +
    365340230711530
def identitySlack1 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    17250226263818240*a*c +
    7889775697006226256*a +
    247974322133613460*b +
    247974322133613460*c +
    18133137359555217620
def helperSlack1 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    120289743931736482266*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    240532800424722506832*a*b +
    24024328103842355868*a*c +
    1020760138552637335710*a +
    4106712350500215270*b^2 +
    8214468378053297790*b*c +
    641499294715168271226*b +
    70687197603919805424*c +
    1818111777843119626536
def g2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    158814778309314*a +
    171801313280*b^2 +
    343602626560*b*c +
    158814778309314*b +
    15092894467401*c +
    560872203414280
def identitySlack2 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    17250226263818240*a*c +
    7889775697006226256*a +
    8625113131909120*b^2 +
    17250226263818240*b*c +
    7889775697006226256*b +
    716042957224112904*c +
    27824582049276012620
def helperSlack2 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    120289743931736482266*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    240532800424722506832*a*b +
    24024328103842355868*a*c +
    1020760138552637335710*a +
    4106712350500215270*b^2 +
    8214468378053297790*b*c +
    641499294715168271226*b +
    70687197603919805424*c +
    1818111777843119626536
def conductor (a b c : ℕ) : ℕ :=
    888359277960*a^3 +
    2665077833880*a^2*b +
    2665077833880*a^2*c +
    159731533706976*a^2 +
    2665077833880*a*b^2 +
    5330155667760*a*b*c +
    319463067413952*a*b +
    49215928147848*a*c +
    1530688391222760*a +
    11104612970220*b^2 +
    22209225940440*b*c +
    946841019611256*b +
    136099601812944*c +
    3190904588684736
def slope (a b : ℕ) : ℕ :=
    388132756013744280*a^2 +
    776265512027488560*a*b +
    24034200516907006668*a +
    8217599409211899540*b +
    70707997705460106849
def intercept (a b : ℕ) : ℕ :=
    129377585337914760*a^3 +
    388132756013744280*a^2*b +
    120329913616607976816*a^2 +
    388132756013744280*a*b^2 +
    240576101140752603132*a*b +
    1021027500358097899260*a +
    4109843381658817020*b^2 +
    641605705131206498001*b +
    1818565885900620042486
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 17 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source28,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source28,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source28,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source28,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source28,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G17

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G18
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source29,source29,source29]
def scale : ℕ := 15
def denominator : ℕ := 11295900
def g0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    14903911056695*a +
    4750350549409*b +
    38028760583600
def identitySlack0 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    706555234073028880*a +
    238486598982529436*b +
    1804994104795837150
def helperSlack0 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    129686683514927870010*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    259322597654187401520*a*b +
    23739665130190750500*a*c +
    1101058253694393084750*a +
    3964396325556677286*b^2 +
    7929836328166221822*b*c +
    690570792452888395794*b +
    69470953746145299534*c +
    1960407143218089416904
def g1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    171287683415910*a +
    4750350549409*b +
    4750350549409*c +
    393447282868750
def identitySlack1 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    17250226263818240*a*c +
    8515965424977771840*a +
    238486598982529436*b +
    238486598982529436*c +
    19544223806056290500
def helperSlack1 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    129686683514927870010*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    259322597654187401520*a*b +
    23739665130190750500*a*c +
    1101058253694393084750*a +
    3964396325556677286*b^2 +
    7929836328166221822*b*c +
    690570792452888395794*b +
    69470953746145299534*c +
    1960407143218089416904
def g2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    171287683415910*a +
    171801313280*b^2 +
    343602626560*b*c +
    171287683415910*b +
    14903911056695*c +
    605094622723480
def identitySlack2 (a b c : ℕ) : ℕ :=
    8625113131909120*a^2 +
    17250226263818240*a*b +
    17250226263818240*a*c +
    8515965424977771840*a +
    8625113131909120*b^2 +
    17250226263818240*b*c +
    8515965424977771840*b +
    706555234073028880*c +
    30044724388275089420
def helperSlack2 (a b c : ℕ) : ℕ :=
    128403486755238660*a^3 +
    386184558848392080*a^2*b +
    387158657431068180*a^2*c +
    129686683514927870010*a^2 +
    387158657431068180*a*b^2 +
    775291413444812460*a*b*c +
    259322597654187401520*a*b +
    23739665130190750500*a*c +
    1101058253694393084750*a +
    3964396325556677286*b^2 +
    7929836328166221822*b*c +
    690570792452888395794*b +
    69470953746145299534*c +
    1960407143218089416904
def conductor (a b c : ℕ) : ℕ :=
    888359277960*a^3 +
    2665077833880*a^2*b +
    2665077833880*a^2*c +
    171458234030160*a^2 +
    2665077833880*a*b^2 +
    5330155667760*a*b*c +
    342916468060320*a*b +
    48860573592600*a*c +
    1647955394454600*a +
    10926935692596*b^2 +
    21853871385192*b*c +
    1016490512439864*b +
    134322829036704*c +
    3436454586361104
def slope (a b : ℕ) : ℕ :=
    388132756013744280*a^2 +
    776265512027488560*a*b +
    23749522081373136600*a +
    7932967359324823572*b +
    69491711327509373034
def intercept (a b : ℕ) : ℕ :=
    129377585337914760*a^3 +
    388132756013744280*a^2*b +
    129728894168258304960*a^2 +
    388132756013744280*a*b^2 +
    259367939338676438220*a*b +
    1101341432095803871500*a +
    3967527356715279036*b^2 +
    690682815532188708669*b +
    1960889311863080568654
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 18 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source29,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source29,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source29,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source29,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source29,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G18

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G19
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source30,source30,source30]
def scale : ℕ := 21
def denominator : ℕ := 22139964
def g0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19826066720490*a +
    6537100722749*b +
    50733649760846
def identitySlack0 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    936994850371278300*a +
    328188604684890796*b +
    2401149644433008434
def helperSlack0 (a b c : ℕ) : ℕ :=
    251124841352773500*a^3 +
    755829252486664272*a^2*b +
    758283980915008044*a^2*c +
    239971804029465606798*a^2 +
    758283980915008044*a*b^2 +
    1519022690258359860*a*b*c +
    479811755520608159712*a*b +
    44337656321448452844*a*c +
    2036610188415588695910*a +
    7650150070780014546*b^2 +
    15302860938500708706*b*c +
    1278111335830729213002*b +
    129998974956289859322*c +
    3626320572268529974020
def g1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    226290442916795*a +
    6537100722749*b +
    6537100722749*c +
    519972000934896
def identitySlack1 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    11243979389666372860*a +
    328188604684890796*b +
    328188604684890796*c +
    25812909318614510484
def helperSlack1 (a b c : ℕ) : ℕ :=
    251124841352773500*a^3 +
    755829252486664272*a^2*b +
    758283980915008044*a^2*c +
    239971804029465606798*a^2 +
    758283980915008044*a*b^2 +
    1519022690258359860*a*b*c +
    479811755520608159712*a*b +
    44337656321448452844*a*c +
    2036610188415588695910*a +
    7650150070780014546*b^2 +
    15302860938500708706*b*c +
    1278111335830729213002*b +
    129998974956289859322*c +
    3626320572268529974020
def g2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    226290442916795*a +
    240521838592*b^2 +
    481043677184*b*c +
    226290442916795*b +
    19826066720490*c +
    799224850894572
def identitySlack2 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    11243979389666372860*a +
    12075158384672768*b^2 +
    24150316769345536*b*c +
    11243979389666372860*b +
    936994850371278300*c +
    39657459943002791988
def helperSlack2 (a b c : ℕ) : ℕ :=
    251124841352773500*a^3 +
    755829252486664272*a^2*b +
    758283980915008044*a^2*c +
    239971804029465606798*a^2 +
    758283980915008044*a*b^2 +
    1519022690258359860*a*b*c +
    479811755520608159712*a*b +
    44337656321448452844*a*c +
    2036610188415588695910*a +
    7650150070780014546*b^2 +
    15302860938500708706*b*c +
    1278111335830729213002*b +
    129998974956289859322*c +
    3626320572268529974020
def conductor (a b c : ℕ) : ℕ :=
    1243702989144*a^3 +
    3731108967432*a^2*b +
    3731108967432*a^2*c +
    227337602292108*a^2 +
    3731108967432*a*b^2 +
    7462217934864*a*b*c +
    454675204584216*a*b +
    66450352975776*a*c +
    2180098298735280*a +
    15191103603060*b^2 +
    30382207206120*b*c +
    1346436739848816*b +
    181762185023496*c +
    4543827563086812
def slope (a b : ℕ) : ℕ :=
    760738709343351816*a^2 +
    1521477418686703632*a*b +
    44362643035547225760*a +
    15310785771636658044*b +
    130051766781357689268
def intercept (a b : ℕ) : ℕ :=
    253579569781117272*a^3 +
    760738709343351816*a^2*b +
    240080166366293996232*a^2 +
    760738709343351816*a*b^2 +
    479928042690572498484*a*b +
    2037339318666286274640*a +
    7658074903915963884*b^2 +
    1278399363736602988419*b +
    3627563440080710709054
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 19 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source30,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source30,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source30,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source30,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source30,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G19


