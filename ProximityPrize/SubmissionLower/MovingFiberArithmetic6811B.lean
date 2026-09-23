import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811A

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 216
def denominator : ℕ := 2342317824
def g0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    194962044502984*a +
    60070879499355*b +
    492337959448646
def identitySlack0 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    9187672162938877376*a +
    3015798434385618420*b +
    23216829117937495384
def helperSlack0 (a b c : ℕ) : ℕ :=
    26625686462997902784*a^3 +
    80079048471097424448*a^2*b +
    80281037553201140544*a^2*c +
    26523955004690097114516*a^2 +
    80281037553201140544*a*b^2 +
    160764064188505997184*a*b*c +
    55259034128744462985672*a*b +
    4538033164680306245064*a*c +
    228003937405959294622152*a +
    731827637212943764764*b^2 +
    1448354095703119186776*b*c +
    147631253065912388373192*b +
    13080278993327836773768*c +
    409200896843792344310868
def g1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2431769693619200*a +
    60070879499355*b +
    58653503919060*c +
    5576003977294006
def identitySlack1 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    248403258198982656*a*c +
    120884161059880454080*a +
    3015798434385618420*b +
    2944640510752488240*c +
    276936692079623620424
def helperSlack1 (a b c : ℕ) : ℕ :=
    26548738241244106176*a^3 +
    79925152027589831232*a^2*b +
    80204089331447343936*a^2*c +
    26523095924755516356756*a^2 +
    80204089331447343936*a*b^2 +
    160687115966752200576*a*b*c +
    55257924967089182388936*a*b +
    4537231620605858726856*a*c +
    228000744132443446123080*a +
    731577555492243925788*b^2 +
    1448104013982419347800*b*c +
    147629190927618823314312*b +
    13078570101215031377928*c +
    409196808646251843706452
def g2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2431769693619200*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2637478136172681*b +
    198741712717104*c +
    8851890406730002
def identitySlack2 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    248403258198982656*a*c +
    120884161059880454080*a +
    124201629099491328*b^2 +
    248403258198982656*b*c +
    131211547709835414204*b +
    9377426625960557856*c +
    439598682846016213208
def helperSlack2 (a b c : ℕ) : ℕ :=
    26500645602647983296*a^3 +
    79828966750397585472*a^2*b +
    80155996692851221056*a^2*c +
    26522104925133658322964*a^2 +
    80155996692851221056*a*b^2 +
    160639023328156077696*a*b*c +
    55256781674111769966024*a*b +
    4536819626940731855304*a*c +
    227995243530866039596104*a +
    731425262136689536668*b^2 +
    1447951720626864958680*b*c +
    147626682678626289449544*b +
    13077755732320766731080*c +
    409188071323523261578068
def conductor (a b c : ℕ) : ℕ :=
    123659611492032*a^3 +
    370978834476096*a^2*b +
    370978834476096*a^2*c +
    28590151635197460*a^2 +
    370978834476096*a*b^2 +
    741957668952192*a*b*c +
    57180303270394920*a*b +
    6530670898750152*a*c +
    276627045490072200*a +
    1452511167581628*b^2 +
    2905022335163256*b*c +
    169560398957513256*b +
    17611501842578952*c +
    577266879920337684
def slope (a b : ℕ) : ℕ :=
    80483026635304856640*a^2 +
    160966053270609713280*a*b +
    4540121988540175541448*a +
    1449003346324166845656*b +
    13084706723171887770120
def intercept (a b : ℕ) : ℕ :=
    26827675545101618880*a^3 +
    80483026635304856640*a^2*b +
    26537157977922790676244*a^2 +
    80483026635304856640*a*b^2 +
    55272886352598204206280*a*b +
    228097148773914556800840*a +
    732476887833991423644*b^2 +
    147666720145070861319816*b +
    409362077182431975432660
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source4,source5,source6,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 378
def denominator : ℕ := 7173348336
def g0 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    354412416629642*a +
    105761858135004*b +
    892468825767628
def identitySlack0 (a b c : ℕ) : ℕ :=
    217352850924109824*a^2 +
    434705701848219648*a*b +
    16742566905718917088*a +
    5309668325809740816*b +
    42179619781948921412
def helperSlack0 (a b c : ℕ) : ℕ :=
    81541181582921430720*a^3 +
    245242136312706922704*a^2*b +
    245860727876649553248*a^2*c +
    71181029067183155763216*a^2 +
    245860727876649553248*a*b^2 +
    492340047317241737040*a*b*c +
    162736698119702752848096*a*b +
    14110958924696682706896*a*c +
    629702075086344867510288*a +
    2253287069483581777212*b^2 +
    4522963138346848543992*b*c +
    439982645132802251722284*b +
    40681457756773159987836*c +
    1152575216014727257786152
def g1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3726443413856800*a +
    105761858135004*b +
    106612283483181*c +
    8556194134690808
def identitySlack1 (a b c : ℕ) : ℕ :=
    217352850924109824*a^2 +
    434705701848219648*a*b +
    434705701848219648*a*c +
    184981657031755527440*a +
    5309668325809740816*b +
    5352363079989618924*c +
    424303400044239175432
def helperSlack1 (a b c : ℕ) : ℕ :=
    81393897877220804400*a^3 +
    244947568901305670064*a^2*b +
    245713444170948926928*a^2*c +
    71179358959847374671960*a^2 +
    245713444170948926928*a*b^2 +
    492192763611541110720*a*b*c +
    162734571432879299815248*a*b +
    14109432083426970535392*a*c +
    629695813351055243090760*a +
    2252830489995909835620*b^2 +
    4522506558859176602400*b*c +
    439978788667300112759592*b +
    40678256790265839735060*c +
    1152567289004839995412944
def g2 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3726443413856800*a +
    4329393094656*b^2 +
    8658786189312*b*c +
    4802892921238176*b +
    345813671442519*c +
    14526576787761536
def identitySlack2 (a b c : ℕ) : ℕ :=
    217352850924109824*a^2 +
    434705701848219648*a*b +
    434705701848219648*a*c +
    184981657031755527440*a +
    217352850924109824*b^2 +
    434705701848219648*b*c +
    239023728100330128144*b +
    16310875502344593996*c +
    720889420569230740744
def helperSlack2 (a b c : ℕ) : ℕ :=
    81099330465819551760*a^3 +
    244358434078503164784*a^2*b +
    245418876759547674288*a^2*c +
    71175400153611869858904*a^2 +
    245418876759547674288*a*b^2 +
    491898196200139858080*a*b*c +
    162729679829841024368832*a*b +
    14106702425040087570288*a*c +
    629678470753112831199072*a +
    2251897693193139202260*b^2 +
    4521573762056405969040*b*c +
    439969231074953875858668*b +
    40672701738521521361784*c +
    1152542763532025470517472
def conductor (a b c : ℕ) : ℕ :=
    395497550547792*a^3 +
    1186492651643376*a^2*b +
    1186492651643376*a^2*c +
    85656228675954552*a^2 +
    1186492651643376*a*b^2 +
    2372985303286752*a*b*c +
    171312457351909104*a*b +
    21079271255471352*a*c +
    826899970468461120*a +
    4691679250273092*b^2 +
    9383358500546184*b*c +
    507787743372308784*b +
    57088185082995528*c +
    1725001092367954632
def slope (a b : ℕ) : ℕ :=
    246479319440592183792*a^2 +
    492958638881184367584*a*b +
    14117365766681245802160*a +
    4524971106201233749488*b +
    40695088866582444602616
def intercept (a b : ℕ) : ℕ :=
    82159773146864061264*a^3 +
    246479319440592183792*a^2*b +
    71218399671629706768552*a^2 +
    246479319440592183792*a*b^2 +
    162776076692003689058928*a*b +
    629963837526763554385032*a +
    2255295037337966982708*b^2 +
    440082981969300116037360*b +
    1153026932631032627196336
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source7,source8,source9,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 27
def denominator : ℕ := 36598716
def g0 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    24748222384285*a +
    7756900663971*b +
    62716955334272
def identitySlack0 (a b c : ℕ) : ℕ :=
    15525203637436416*a^2 +
    31050407274872832*a*b +
    1167434466669527720*a +
    389427440934000084*b +
    2961078800824000438
def helperSlack0 (a b c : ℕ) : ℕ :=
    414372833397871272*a^3 +
    1247927764053226104*a^2*b +
    1252737027912838392*a^2*c +
    412116668578824970104*a^2 +
    1252737027912838392*a*b^2 +
    2510283319685289072*a*b*c +
    823937857058753970408*a*b +
    71280507765602472192*a*c +
    3498463066798431641448*a +
    11767191865233345072*b^2 +
    23539293187323377688*b*c +
    2191094600714268957522*b +
    206725392661390218864*c +
    6226516085390605560636
def g1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    302270361006046*a +
    7756900663971*b +
    7756900663971*c +
    693450610894082
def identitySlack1 (a b c : ℕ) : ℕ :=
    15525203637436416*a^2 +
    31050407274872832*a*b +
    31050407274872832*a*c +
    15025130624125300544*a +
    389427440934000084*b +
    389427440934000084*c +
    34438868019770910628
def helperSlack1 (a b c : ℕ) : ℕ :=
    414372833397871272*a^3 +
    1247927764053226104*a^2*b +
    1252737027912838392*a^2*c +
    412116668578824970104*a^2 +
    1252737027912838392*a*b^2 +
    2510283319685289072*a*b*c +
    823937857058753970408*a*b +
    71280507765602472192*a*c +
    3498463066798431641448*a +
    11767191865233345072*b^2 +
    23539293187323377688*b*c +
    2191094600714268957522*b +
    206725392661390218864*c +
    6226516085390605560636
def g2 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    302270361006046*a +
    309242363904*b^2 +
    618484727808*b*c +
    302270361006046*b +
    24748222384285*c +
    1067729147903864
def identitySlack2 (a b c : ℕ) : ℕ :=
    15525203637436416*a^2 +
    31050407274872832*a*b +
    31050407274872832*a*c +
    15025130624125300544*a +
    15525203637436416*b^2 +
    31050407274872832*b*c +
    15025130624125300544*b +
    1167434466669527720*c +
    53004071249683487356
def helperSlack2 (a b c : ℕ) : ℕ :=
    414372833397871272*a^3 +
    1247927764053226104*a^2*b +
    1252737027912838392*a^2*c +
    412116668578824970104*a^2 +
    1252737027912838392*a*b^2 +
    2510283319685289072*a*b*c +
    823937857058753970408*a*b +
    71280507765602472192*a*c +
    3498463066798431641448*a +
    11767191865233345072*b^2 +
    23539293187323377688*b*c +
    2191094600714268957522*b +
    206725392661390218864*c +
    6226516085390605560636
def conductor (a b c : ℕ) : ℕ :=
    1599046700328*a^3 +
    4797140100984*a^2*b +
    4797140100984*a^2*c +
    302939148370320*a^2 +
    4797140100984*a*b^2 +
    9594280201968*a*b*c +
    605878296740640*a*b +
    84040132358952*a*c +
    2909462981178600*a +
    18922239680652*b^2 +
    37844479361304*b*c +
    1792583906823864*b +
    227069413678800*c +
    6063234146622576
def slope (a b : ℕ) : ℕ :=
    1257546291772450680*a^2 +
    2515092583544901360*a*b +
    71330103305270065800*a +
    23554873198368579996*b +
    206830708047513509454
def intercept (a b : ℕ) : ℕ :=
    419182097257483560*a^3 +
    1257546291772450680*a^2*b +
    412347602486562395328*a^2 +
    1257546291772450680*a*b^2 +
    824184370977536597940*a*b +
    3500036125358289516252*a +
    11782771876278547380*b^2 +
    2191710532080594960171*b +
    6229208009865788710506
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source10,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source10,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source10,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 840
def denominator : ℕ := 35423942400
def g0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    801546922301370*a +
    246365356053480*b +
    2029431656470340
def identitySlack0 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    37906741556649913080*a +
    12368526335308909920*b +
    96050286555016783360
def helperSlack0 (a b c : ℕ) : ℕ :=
    402963651680979721920*a^3 +
    1211654797421518820160*a^2*b +
    1214418639800098474560*a^2*c +
    348893114324867446875828*a^2 +
    1214418639800098474560*a*b^2 +
    2431601121978776603520*a*b*c +
    746667179694598824634056*a*b +
    71054485314871482239088*a*c +
    3021392440206133988767080*a +
    11606061113536274648676*b^2 +
    23149067810207605094472*b*c +
    2005290192993984138767112*b +
    205855082108788994050848*c +
    5455555183687400148503412
def g1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8219618251038635*a +
    246365356053480*b +
    244853488767832*c +
    18888725367645990
def identitySlack1 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    407989474414007498740*a +
    12368526335308909920*b +
    12292624550100237728*c +
    936618967704458949960
def helperSlack1 (a b c : ℕ) : ℕ :=
    401799928574209341120*a^3 +
    1209327351207978058560*a^2*b +
    1213254916693328093760*a^2*c +
    348875127754930996482228*a^2 +
    1213254916693328093760*a*b^2 +
    2430437398872006222720*a*b*c +
    746645411024565370502856*a*b +
    71042314709233413599088*a*c +
    3021305438082422009599080*a +
    11602279013439270911076*b^2 +
    23145285710110601356872*b*c +
    2005245271977523119080712*b +
    205829104409489348094048*c +
    5455424675600351186346612
def g2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8219618251038635*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9384228519514360*b +
    786995199677008*c +
    30501410643042630
def identitySlack2 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    407989474414007498740*a +
    483006335386910720*b^2 +
    966012670773821440*b*c +
    466457568332562796640*b +
    37176186874016443232*c +
    1512619841070980168520
def helperSlack2 (a b c : ℕ) : ℕ :=
    401072601632477853120*a^3 +
    1207872697324515082560*a^2*b +
    1212527589751596605760*a^2*c +
    348865134726637354040628*a^2 +
    1212527589751596605760*a*b^2 +
    2429710071930274734720*a*b*c +
    746633114794289578349256*a*b +
    71035599056213241771888*a*c +
    3021260927249745975074280*a +
    11599975811457121199076*b^2 +
    23142982508128451644872*b*c +
    2005221072939348692082312*b +
    205815454903979208361248*c +
    5455361122949570500919412
def conductor (a b c : ℕ) : ℕ :=
    2172334554371520*a^3 +
    6517003663114560*a^2*b +
    6517003663114560*a^2*c +
    462625109592443028*a^2 +
    6517003663114560*a*b^2 +
    13034007326229120*a*b*c +
    925250219184886056*a*b +
    116609479839922608*a*c +
    4463326004346566280*a +
    26109412115739876*b^2 +
    52218824231479752*b*c +
    2743331229092211912*b +
    317409011057321568*c +
    9311238664181327412
def slope (a b : ℕ) : ℕ :=
    1217182482178678128960*a^2 +
    2434364964357356257920*a*b +
    71082681359493707058288*a +
    23157965443128120297672*b +
    205914638075779082190048
def intercept (a b : ℕ) : ℕ :=
    405727494059559376320*a^3 +
    1217182482178678128960*a^2*b +
    349053259363209065298228*a^2 +
    1217182482178678128960*a*b^2 +
    746836222365860958259656*a*b +
    3022508896397958455675880*a +
    11614958746456789851876*b^2 +
    2005719184267640935482312*b +
    5457478671084251188372212
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source11,source12,source13,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7

