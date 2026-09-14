import ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6811

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G0
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source0,source0,source0]
def scale : ℕ := 6
def denominator : ℕ := 1807668
def g0 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    5282919677981*a +
    1649298112492*b +
    13426426904882
def identitySlack0 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    248600814597728725*a +
    82816206122560796*b +
    632505096193011796
def helperSlack0 (a b c : ℕ) : ℕ :=
    30877497346320612*a^3 +
    92810612922651180*a^2*b +
    92988733806340524*a^2*c +
    14223872521181535957*a^2 +
    92988733806340524*a*b^2 +
    186155588496370392*a*b*c +
    28439687141179215786*a*b +
    3493697932723036518*a*c +
    121547011929064533612*a +
    589887076269323772*b^2 +
    1179952273422336888*b*c +
    76340965578626257032*b +
    9815504358218116896*c +
    219930591368294165535
def g1 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    206158430160*a*c +
    46670171801187*a +
    1649298112492*b +
    1649298112492*c +
    109996997610942
def identitySlack1 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    10351833253624080*a*c +
    2310108474267540375*a +
    82816206122560796*b +
    82816206122560796*c +
    5439927085074574506
def helperSlack1 (a b c : ℕ) : ℕ :=
    30877497346320612*a^3 +
    92810612922651180*a^2*b +
    92988733806340524*a^2*c +
    14223872521181535957*a^2 +
    92988733806340524*a*b^2 +
    186155588496370392*a*b*c +
    28439687141179215786*a*b +
    3493697932723036518*a*c +
    121547011929064533612*a +
    589887076269323772*b^2 +
    1179952273422336888*b*c +
    76340965578626257032*b +
    9815504358218116896*c +
    219930591368294165535
def g2 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    206158430160*a*c +
    46670171801187*a +
    103079215080*b^2 +
    206158430160*b*c +
    46670171801187*b +
    5282919677981*c +
    169853941979916
def identitySlack2 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    10351833253624080*a*c +
    2310108474267540375*a +
    5175916626812040*b^2 +
    10351833253624080*b*c +
    2310108474267540375*b +
    248600814597728725*c +
    8395512411911346048
def helperSlack2 (a b c : ℕ) : ℕ :=
    30877497346320612*a^3 +
    92810612922651180*a^2*b +
    92988733806340524*a^2*c +
    14223872521181535957*a^2 +
    92988733806340524*a*b^2 +
    186155588496370392*a*b*c +
    28439687141179215786*a*b +
    3493697932723036518*a*c +
    121547011929064533612*a +
    589887076269323772*b^2 +
    1179952273422336888*b*c +
    76340965578626257032*b +
    9815504358218116896*c +
    219930591368294165535
def conductor (a b c : ℕ) : ℕ :=
    118469137716*a^3 +
    355407413148*a^2*b +
    355407413148*a^2*c +
    19222158990987*a^2 +
    355407413148*a*b^2 +
    710814826296*a*b*c +
    38444317981974*a*b +
    6733111081722*a*c +
    183336404581170*a +
    1461135031620*b^2 +
    2922270063240*b*c +
    113713938396294*b +
    18580317695538*c +
    381788100711663
def slope (a b : ℕ) : ℕ :=
    93166854690029868*a^2 +
    186333709380059736*a*b +
    3495553358821294662*a +
    1180531166294327256*b +
    9819460126997759016
def intercept (a b : ℕ) : ℕ :=
    31055618230009956*a^3 +
    93166854690029868*a^2*b +
    14230984581925222293*a^2 +
    93166854690029868*a*b^2 +
    28447378094794892490*a*b +
    121594110513471829044*a +
    590465969141314140*b^2 +
    76359828534221602632*b +
    220010502259108245111
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 0 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source0,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source0,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source0,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source0,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source0,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G0

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source1,source1,source1]
def scale : ℕ := 7
def denominator : ℕ := 2460437
def g0 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    5394589548548*a +
    1752378507234*b +
    13641179463964
def identitySlack0 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    251429688609720958*a +
    87992181983740842*b +
    636342453445224917
def helperSlack0 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    26029328908778619894*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    52040828052270729674*a*b +
    4214785918615393088*a*c +
    223231909229828706441*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    139258104129706051802*b +
    11717404972261724432*c +
    403659660588935204431
def g1 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    240518168520*a*c +
    73402658261587*a +
    1752378507234*b +
    1752378507234*c +
    172327191975354
def identitySlack1 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    12077138795894760*a*c +
    3646870006506028499*a +
    87992181983740842*b +
    87992181983740842*c +
    8555821108700851572
def helperSlack1 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    26029328908778619894*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    52040828052270729674*a*b +
    4214785918615393088*a*c +
    223231909229828706441*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    139258104129706051802*b +
    11717404972261724432*c +
    403659660588935204431
def g2 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    240518168520*a*c +
    73402658261587*a +
    120259084260*b^2 +
    240518168520*b*c +
    73402658261587*b +
    5394589548548*c +
    267661919005452
def identitySlack2 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    12077138795894760*a*c +
    3646870006506028499*a +
    6038569397947380*b^2 +
    12077138795894760*b*c +
    3646870006506028499*b +
    251429688609720958*c +
    13284517099506889206
def helperSlack2 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    26029328908778619894*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    52040828052270729674*a*b +
    4214785918615393088*a*c +
    223231909229828706441*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    139258104129706051802*b +
    11717404972261724432*c +
    403659660588935204431
def conductor (a b c : ℕ) : ℕ :=
    138213994002*a^3 +
    414641982006*a^2*b +
    414641982006*a^2*c +
    29687244645297*a^2 +
    414641982006*a*b^2 +
    829283964012*a*b*c +
    59374489290594*a*b +
    7266223406556*a*c +
    286506396902820*a +
    1638839340750*b^2 +
    3277678681500*b*c +
    175971343612656*b +
    19646545960542*c +
    597645420317769
def slope (a b : ℕ) : ℕ :=
    126810371998876986*a^2 +
    253620743997753972*a*b +
    4217390490183879836*a +
    1486079438897301072*b +
    11722939897778243894
def intercept (a b : ℕ) : ℕ :=
    42270123999625662*a^3 +
    126810371998876986*a^2*b +
    26042614257404470034*a^2 +
    126810371998876986*a*b^2 +
    52054933327333207672*a*b +
    223323496463867578243*a +
    743322568814879448*b^2 +
    139293646998006965286*b +
    403816969339673873625
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 1 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source1,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source1,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source1,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source1,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source1,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source2,source2,source2]
def scale : ℕ := 7
def denominator : ℕ := 2460437
def g0 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    5523441516553*a +
    1752378507234*b +
    13941835039014
def identitySlack0 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    257899732479156023*a +
    87992181983740842*b +
    651439271835210567
def helperSlack0 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    23899133218637530294*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    47781985608994089754*a*b +
    4305400304058376888*a*c +
    204771572454337354396*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    127901044082954647167*b +
    11959046517926539347*c +
    370289346039887984946
def g1 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    240518168520*a*c +
    67346615765352*a +
    1752378507234*b +
    1752378507234*c +
    158196379948004
def identitySlack1 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    12077138795894760*a*c +
    3342777944642580444*a +
    87992181983740842*b +
    87992181983740842*c +
    7846270644371526022
def helperSlack1 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    23899133218637530294*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    47781985608994089754*a*b +
    4305400304058376888*a*c +
    204771572454337354396*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    127901044082954647167*b +
    11959046517926539347*c +
    370289346039887984946
def g2 (a b c : ℕ) : ℕ :=
    120259084260*a^2 +
    240518168520*a*b +
    240518168520*a*c +
    67346615765352*a +
    120259084260*b^2 +
    240518168520*b*c +
    67346615765352*b +
    5523441516553*c +
    245456260441952
def identitySlack2 (a b c : ℕ) : ℕ :=
    6038569397947380*a^2 +
    12077138795894760*a*b +
    12077138795894760*a*c +
    3342777944642580444*a +
    6038569397947380*b^2 +
    12077138795894760*b*c +
    3342777944642580444*b +
    257899732479156023*c +
    12169504366057863706
def helperSlack2 (a b c : ℕ) : ℕ :=
    42017579922635562*a^3 +
    126305283844896786*a^2*b +
    126557827921886886*a^2*c +
    23899133218637530294*a^2 +
    126557827921886886*a*b^2 +
    253368199920763872*a*b*c +
    47781985608994089754*a*b +
    4305400304058376888*a*c +
    204771572454337354396*a +
    742502642378251590*b^2 +
    1485259512460673214*b*c +
    127901044082954647167*b +
    11959046517926539347*c +
    370289346039887984946
def conductor (a b c : ℕ) : ℕ :=
    138213994002*a^3 +
    414641982006*a^2*b +
    414641982006*a^2*c +
    27367153231362*a^2 +
    414641982006*a*b^2 +
    829283964012*a*b*c +
    54734306462724*a*b +
    7364950700766*a*c +
    263305482763470*a +
    1638839340750*b^2 +
    3277678681500*b*c +
    162050795129046*b +
    19942727843172*c +
    548923500625134
def slope (a b : ℕ) : ℕ :=
    126810371998876986*a^2 +
    253620743997753972*a*b +
    4308021711898662976*a +
    1486079438897301072*b +
    11964627743190506994
def intercept (a b : ℕ) : ℕ :=
    42270123999625662*a^3 +
    126810371998876986*a^2*b +
    23911644098760610794*a^2 +
    126810371998876986*a*b^2 +
    47795316415553798112*a*b +
    204857158550769550063*a +
    743322568814879448*b^2 +
    127934457162872944141*b +
    370436008828582937315
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 2 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source2,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source2,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source2,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source2,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source2,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source3,source3,source3]
def scale : ℕ := 6
def denominator : ℕ := 1807668
def g0 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    4715971018759*a +
    1443134963684*b +
    11828653981942
def identitySlack0 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    220132621572214439*a +
    72464135931464692*b +
    552276124413425576
def helperSlack0 (a b c : ℕ) : ℕ :=
    30899762456781780*a^3 +
    92855143143573516*a^2*b +
    93010998916801692*a^2*c +
    21884232608580197907*a^2 +
    93010998916801692*a*b^2 +
    186177853606831560*a*b*c +
    43755428949762211038*a*b +
    3152090314600312914*a*c +
    187931306082840813084*a +
    527790656498467068*b^2 +
    1055743353523068192*b*c +
    116975840702258733564*b +
    8697237241718387952*c +
    339765588001170042369
def g1 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    206158430160*a*c +
    72079779891773*a +
    1443134963684*b +
    1443134963684*c +
    169011388618082
def identitySlack1 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    10351833253624080*a*c +
    3586001125320135193*a +
    72464135931464692*b +
    72464135931464692*c +
    8403216700716095326
def helperSlack1 (a b c : ℕ) : ℕ :=
    30899762456781780*a^3 +
    92855143143573516*a^2*b +
    93010998916801692*a^2*c +
    21884232608580197907*a^2 +
    93010998916801692*a*b^2 +
    186177853606831560*a*b*c +
    43755428949762211038*a*b +
    3152090314600312914*a*c +
    187931306082840813084*a +
    527790656498467068*b^2 +
    1055743353523068192*b*c +
    116975840702258733564*b +
    8697237241718387952*c +
    339765588001170042369
def g2 (a b c : ℕ) : ℕ :=
    103079215080*a^2 +
    206158430160*a*b +
    206158430160*a*c +
    72079779891773*a +
    103079215080*b^2 +
    206158430160*b*c +
    72079779891773*b +
    4715971018759*c +
    263023215782516
def identitySlack2 (a b c : ℕ) : ℕ :=
    5175916626812040*a^2 +
    10351833253624080*a*b +
    10351833253624080*a*c +
    3586001125320135193*a +
    5175916626812040*b^2 +
    10351833253624080*b*c +
    3586001125320135193*b +
    220132621572214439*c +
    13073821157361299848
def helperSlack2 (a b c : ℕ) : ℕ :=
    30899762456781780*a^3 +
    92855143143573516*a^2*b +
    93010998916801692*a^2*c +
    21884232608580197907*a^2 +
    93010998916801692*a*b^2 +
    186177853606831560*a*b*c +
    43755428949762211038*a*b +
    3152090314600312914*a*c +
    187931306082840813084*a +
    527790656498467068*b^2 +
    1055743353523068192*b*c +
    116975840702258733564*b +
    8697237241718387952*c +
    339765588001170042369
def conductor (a b c : ℕ) : ℕ :=
    118469137716*a^3 +
    355407413148*a^2*b +
    355407413148*a^2*c +
    28956670200093*a^2 +
    355407413148*a*b^2 +
    710814826296*a*b*c +
    57913340400186*a*b +
    6298710987198*a*c +
    280681516672230*a +
    1382153196252*b^2 +
    2764306392504*b*c +
    171805078309458*b +
    16961190070494*c +
    585896908761417
def slope (a b : ℕ) : ℕ :=
    93166854690029868*a^2 +
    186333709380059736*a*b +
    3153711957010417026*a +
    1056246792409606824*b +
    8700686479126510056
def intercept (a b : ℕ) : ℕ :=
    31055618230009956*a^3 +
    93166854690029868*a^2*b +
    21893445371285625843*a^2 +
    93166854690029868*a*b^2 +
    43765145151354177606*a*b +
    187995680531468303052*a +
    528294095385005700*b^2 +
    117000544887226709472*b +
    339876583070533771929
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 3 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : (cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, (cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source3,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
    MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,
    flagMixed,unitZFlag,unitYZFlag,unitAllFlag,g0,g1,g2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80861*identityDegree f a b c ≤ 50213*graph cfg scale f a b c := by
  have he : 50213*graph cfg scale f a b c = scale*131073*80861*identityDegree f a b c+
      (f.zOnly*identitySlack0 a b c+f.yz*identitySlack1 a b c+f.all*identitySlack2 a b c) := by
    rw [graph_eq]
    simp only [scale,identityDegree,g0,g1,g2,identitySlack0,identitySlack1,identitySlack2]
    ring
  rw [he]
  exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50213*graph cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  rw [graph_eq]
  norm_num [cfg,scale,source3,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50213 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source3,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source3,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source3,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50213
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graph cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50213) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graph cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50213)*50213 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3


