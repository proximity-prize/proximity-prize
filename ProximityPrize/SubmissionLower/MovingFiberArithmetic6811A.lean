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
def scale : ℕ := 18
def denominator : ℕ := 16266096
def g0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    18924102026917*a +
    5738217341432*b +
    48044916609338
def identitySlack0 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    900048758218596788*a +
    288081463409252128*b +
    2287004843603344252
def helperSlack0 (a b c : ℕ) : ℕ :=
    184700421727166448*a^3 +
    555704353134703440*a^2*b +
    557307441087907536*a^2*c +
    157375187951781355776*a^2 +
    557307441087907536*a*b^2 +
    1116217970129019168*a*b*c +
    314676741533093949024*a*b +
    36064378550026429992*a*c +
    1334522101697235643104*a +
    5742783732219331824*b^2 +
    11487170552391867744*b*c +
    839658075420501199944*b +
    105106985654789372256*c +
    2377151459275349152224
def g1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    173040073457660*a +
    5738217341432*b +
    5738217341432*c +
    398309333435368
def identitySlack1 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    20700271516581888*a*c +
    8587270127986874080*a +
    288081463409252128*b +
    288081463409252128*c +
    19746637476085493672
def helperSlack1 (a b c : ℕ) : ℕ :=
    184700421727166448*a^3 +
    555704353134703440*a^2*b +
    557307441087907536*a^2*c +
    157375187951781355776*a^2 +
    557307441087907536*a*b^2 +
    1116217970129019168*a*b*c +
    314676741533093949024*a*b +
    36064378550026429992*a*c +
    1334522101697235643104*a +
    5742783732219331824*b^2 +
    11487170552391867744*b*c +
    839658075420501199944*b +
    105106985654789372256*c +
    2377151459275349152224
def g2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    173040073457660*a +
    206161575936*b^2 +
    412323151872*b*c +
    173040073457660*b +
    18924102026917*c +
    610867242401776
def identitySlack2 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    20700271516581888*a*c +
    8587270127986874080*a +
    10350135758290944*b^2 +
    20700271516581888*b*c +
    8587270127986874080*b +
    900048758218596788*c +
    30267843776417361704
def helperSlack2 (a b c : ℕ) : ℕ :=
    184700421727166448*a^3 +
    555704353134703440*a^2*b +
    557307441087907536*a^2*c +
    157375187951781355776*a^2 +
    557307441087907536*a*b^2 +
    1116217970129019168*a*b*c +
    314676741533093949024*a*b +
    36064378550026429992*a*c +
    1334522101697235643104*a +
    5742783732219331824*b^2 +
    11487170552391867744*b*c +
    839658075420501199944*b +
    105106985654789372256*c +
    2377151459275349152224
def conductor (a b c : ℕ) : ℕ :=
    1066031133552*a^3 +
    3198093400656*a^2*b +
    3198093400656*a^2*c +
    175189389084864*a^2 +
    3198093400656*a*b^2 +
    6396186801312*a*b*c +
    350378778169728*a*b +
    60587138364984*a*c +
    1671941555832240*a +
    13147858286640*b^2 +
    26295716573280*b*c +
    1036567806241968*b +
    167192886827736*c +
    3482117318677536
def slope (a b : ℕ) : ℕ :=
    558910529041111632*a^2 +
    1117821058082223264*a*b +
    36081077384910753288*a +
    11492380588239781056*b +
    105142587573806151336
def intercept (a b : ℕ) : ℕ :=
    186303509680370544*a^3 +
    558910529041111632*a^2*b +
    157439753121945063024*a^2 +
    558910529041111632*a*b^2 +
    314746516739105569584*a*b +
    1334950302772159231752*a +
    5747993768067245136*b^2 +
    839829372731648644356*b +
    2377878310807970372352
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 0 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source0,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source0,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G0

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source1,source1,source1]
def scale : ℕ := 21
def denominator : ℕ := 22139964
def g0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19259116488372*a +
    6064642195984*b +
    48843803726216
def identitySlack0 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    908531680918026228*a +
    304469296807180736*b +
    2306271814110443914
def helperSlack0 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    291209979940048524978*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    582255491688255054096*a*b +
    43143020381388860772*a*c +
    2474429866935693884910*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1546560399084040520586*b +
    125217508601835606390*c +
    4402876704162585815712
def g1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    274859179468237*a +
    6064642195984*b +
    6064642195984*c +
    629754439847866
def identitySlack1 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    13682324239494967028*a +
    304469296807180736*b +
    304469296807180736*c +
    31324426881801256364
def helperSlack1 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    291209979940048524978*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    582255491688255054096*a*b +
    43143020381388860772*a*c +
    2474429866935693884910*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1546560399084040520586*b +
    125217508601835606390*c +
    4402876704162585815712
def g2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    274859179468237*a +
    240521838592*b^2 +
    481043677184*b*c +
    274859179468237*b +
    19259116488372*c +
    971424271537972
def identitySlack2 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    13682324239494967028*a +
    12075158384672768*b^2 +
    24150316769345536*b*c +
    13682324239494967028*b +
    908531680918026228*c +
    48302559656984045588
def helperSlack2 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    291209979940048524978*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    582255491688255054096*a*b +
    43143020381388860772*a*c +
    2474429866935693884910*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1546560399084040520586*b +
    125217508601835606390*c +
    4402876704162585815712
def conductor (a b c : ℕ) : ℕ :=
    1243702989144*a^3 +
    3731108967432*a^2*b +
    3731108967432*a^2*c +
    273000662641476*a^2 +
    3731108967432*a*b^2 +
    7462217934864*a*b*c +
    546001325282952*a*b +
    65384289310032*a*c +
    2636728902228960*a +
    14746910409000*b^2 +
    29493820818000*b*c +
    1618638329168784*b +
    176787221250024*c +
    5500975057647300
def slope (a b : ℕ) : ℕ :=
    760738709343351816*a^2 +
    1521477418686703632*a*b +
    43166461525505241504*a +
    14314301204783298096*b +
    125267322931484281548
def intercept (a b : ℕ) : ℕ :=
    253579569781117272*a^3 +
    760738709343351816*a^2*b +
    291331548220687056180*a^2 +
    760738709343351816*a*b^2 +
    582384439306823236020*a*b +
    2475269653130001301266*a +
    7159696246687709256*b^2 +
    1546885785286721934747*b +
    4404319984813964735352
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 1 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source1,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source1,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source2,source2,source2]
def scale : ℕ := 21
def denominator : ℕ := 22139964
def g0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19731575015137*a +
    6064642195984*b +
    49917575696866
def identitySlack0 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    932250988795736288*a +
    304469296807180736*b +
    2360179462124956514
def helperSlack0 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    266588880244576737162*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    533027960057303063472*a*b +
    44139535253531459532*a*c +
    2264042437912673936826*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1416776907057936322458*b +
    127844721667049336460*c +
    4029102520086275609292
def g1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    251519728246046*a +
    6064642195984*b +
    6064642195984*c +
    576710104497756
def identitySlack1 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    12510590430336090064*a +
    304469296807180736*b +
    304469296807180736*c +
    28661389069884333924
def helperSlack1 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    266588880244576737162*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    533027960057303063472*a*b +
    44139535253531459532*a*c +
    2264042437912673936826*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1416776907057936322458*b +
    127844721667049336460*c +
    4029102520086275609292
def g2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    251519728246046*a +
    240521838592*b^2 +
    481043677184*b*c +
    251519728246046*b +
    19731575015137*c +
    888674744497272
def identitySlack2 (a b c : ℕ) : ℕ :=
    12075158384672768*a^2 +
    24150316769345536*a*b +
    24150316769345536*a*c +
    12510590430336090064*a +
    12075158384672768*b^2 +
    24150316769345536*b*c +
    12510590430336090064*b +
    932250988795736288*c +
    44148202401432742788
def helperSlack2 (a b c : ℕ) : ℕ :=
    251306673088206372*a^3 +
    756192915957530016*a^2*b +
    758465812650440916*a^2*c +
    266588880244576737162*a^2 +
    758465812650440916*a*b^2 +
    1519204521993792732*a*b*c +
    533027960057303063472*a*b +
    44139535253531459532*a*c +
    2264042437912673936826*a +
    7152316908758058534*b^2 +
    14306921866853647374*b*c +
    1416776907057936322458*b +
    127844721667049336460*c +
    4029102520086275609292
def conductor (a b c : ℕ) : ℕ :=
    1243702989144*a^3 +
    3731108967432*a^2*b +
    3731108967432*a^2*c +
    251057518854912*a^2 +
    3731108967432*a*b^2 +
    7462217934864*a*b*c +
    502115037709824*a*b +
    66272675698152*a*c +
    2417297464363320*a +
    14746910409000*b^2 +
    29493820818000*b*c +
    1486979466449400*b +
    179452380414384*c +
    5040169038129456
def slope (a b : ℕ) : ℕ :=
    760738709343351816*a^2 +
    1521477418686703632*a*b +
    44163127924094034324*a +
    14314301204783298096*b +
    127894952694425045283
def intercept (a b : ℕ) : ℕ :=
    253579569781117272*a^3 +
    760738709343351816*a^2*b +
    266703114645219475860*a^2 +
    760738709343351816*a*b^2 +
    533149573795875452892*a*b +
    2264825395475320031970*a +
    7159696246687709256*b^2 +
    1417082125090629307233*b +
    4030444986702630594084
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 2 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source2,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source2,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source3,source3,source3]
def scale : ℕ := 18
def denominator : ℕ := 16266096
def g0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    16845284509151*a +
    4982283698608*b +
    42358208466718
def identitySlack0 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    795683803556672524*a +
    250130570804916032*b +
    2001509348011249772
def helperSlack0 (a b c : ℕ) : ℕ :=
    184900807721316960*a^3 +
    556105125123004464*a^2*b +
    557507827082058048*a^2*c +
    245715118924136667408*a^2 +
    557507827082058048*a*b^2 +
    1116418356123169680*a*b*c +
    491309660731807717200*a*b +
    32307336466548929928*a*c +
    2089381496794919142552*a +
    5059811677850169192*b^2 +
    10121081720435544888*b*c +
    1303092048449261138616*b +
    92963958329615311080*c +
    3716487613849477053096
def g1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    270744496792662*a +
    4982283698608*b +
    4982283698608*c +
    619403265494028
def identitySlack1 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    20700271516581888*a*c +
    13492422997097314488*a +
    250130570804916032*b +
    250130570804916032*c +
    30846437241158460312
def helperSlack1 (a b c : ℕ) : ℕ :=
    184900807721316960*a^3 +
    556105125123004464*a^2*b +
    557507827082058048*a^2*c +
    245715118924136667408*a^2 +
    557507827082058048*a*b^2 +
    1116418356123169680*a*b*c +
    491309660731807717200*a*b +
    32307336466548929928*a*c +
    2089381496794919142552*a +
    5059811677850169192*b^2 +
    10121081720435544888*b*c +
    1303092048449261138616*b +
    92963958329615311080*c +
    3716487613849477053096
def g2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    270744496792662*a +
    206161575936*b^2 +
    412323151872*b*c +
    270744496792662*b +
    16845284509151*c +
    957276193657176
def identitySlack2 (a b c : ℕ) : ℕ :=
    10350135758290944*a^2 +
    20700271516581888*a*b +
    20700271516581888*a*c +
    13492422997097314488*a +
    10350135758290944*b^2 +
    20700271516581888*b*c +
    13492422997097314488*b +
    795683803556672524*c +
    47658958765243463304
def helperSlack2 (a b c : ℕ) : ℕ :=
    184900807721316960*a^3 +
    556105125123004464*a^2*b +
    557507827082058048*a^2*c +
    245715118924136667408*a^2 +
    557507827082058048*a*b^2 +
    1116418356123169680*a*b*c +
    491309660731807717200*a*b +
    32307336466548929928*a*c +
    2089381496794919142552*a +
    5059811677850169192*b^2 +
    10121081720435544888*b*c +
    1303092048449261138616*b +
    92963958329615311080*c +
    3716487613849477053096
def conductor (a b c : ℕ) : ℕ :=
    1066031133552*a^3 +
    3198093400656*a^2*b +
    3198093400656*a^2*c +
    267048541616472*a^2 +
    3198093400656*a*b^2 +
    6396186801312*a*b*c +
    534097083232944*a*b +
    56678238257256*a*c +
    2590533081148320*a +
    12437149176144*b^2 +
    24874298352288*b*c +
    1584879884989632*b +
    152623350062568*c +
    5408316685399320
def slope (a b : ℕ) : ℕ :=
    558910529041111632*a^2 +
    1117821058082223264*a*b +
    32321931248239866936*a +
    10125612670414392576*b +
    92995001466288410016
def intercept (a b : ℕ) : ℕ :=
    186303509680370544*a^3 +
    558910529041111632*a^2*b +
    245799659137794559992*a^2 +
    558910529041111632*a*b^2 +
    491398731895444457472*a*b +
    2089973463277390982280*a +
    5064342627829016880*b^2 +
    1303318855821399233652*b +
    3717508917983440915512
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 3 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source3,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source3,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3


