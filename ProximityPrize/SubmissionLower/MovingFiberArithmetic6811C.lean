import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811B

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 840
def denominator : ℕ := 35423942400
def g0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    801546922301370*a +
    242585687839360*b +
    2024621099111540
def identitySlack0 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    37906741556649913080*a +
    12178771872287229440*b +
    95808777333375588160
def helperSlack0 (a b c : ℕ) : ℕ :=
    402963651680979721920*a^3 +
    1211654797421518820160*a^2*b +
    1214418639800098474560*a^2*c +
    348897385289563290383028*a^2 +
    1214418639800098474560*a*b^2 +
    2431601121978776603520*a*b*c +
    760060481061612679488456*a*b +
    71054679742528684299888*a*c +
    3038466342184406133803880*a +
    11446618828754673579876*b^2 +
    22989625478045396659272*b*c +
    2044947165974381024480712*b +
    205652639868463039868448*c +
    5506330357837791038625012
def g1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8219618251038635*a +
    242585687839360*b +
    244853488767832*c +
    18883914810287190
def identitySlack1 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    407989474414007498740*a +
    12178771872287229440*b +
    12292624550100237728*c +
    936377458482817754760
def helperSlack1 (a b c : ℕ) : ℕ :=
    401799928574209341120*a^3 +
    1209327351207978058560*a^2*b +
    1213254916693328093760*a^2*c +
    348875131734902015259828*a^2 +
    1213254916693328093760*a*b^2 +
    2430437398872006222720*a*b*c +
    760034493895317182726856*a*b +
    71042315183039487263088*a*c +
    3038346368561134930687080*a +
    11442885217120451941476*b^2 +
    22985891866411175020872*b*c +
    2044890865156201099112712*b +
    205626237895206535652448*c +
    5506141695534871143210612
def g2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8219618251038635*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9701720649500440*b +
    786995199677008*c +
    30905497461181830
def identitySlack2 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    407989474414007498740*a +
    483006335386910720*b^2 +
    966012670773821440*b*c +
    482396943226383956960*b +
    37176186874016443232*c +
    1532906615688840565320
def helperSlack2 (a b c : ℕ) : ℕ :=
    401072601632477853120*a^3 +
    1207872697324515082560*a^2*b +
    1212527589751596605760*a^2*c +
    348869405691333197547828*a^2 +
    1212527589751596605760*a*b^2 +
    2429710071930274734720*a*b*c +
    760026416161303433203656*a*b +
    71035793483870443832688*a*c +
    3038334829228018120111080*a +
    11440533526675520130276*b^2 +
    22983540175966243209672*b*c +
    2044878045919745577795912*b +
    205613012663653254178848*c +
    5506136297099961391041012
def conductor (a b c : ℕ) : ℕ :=
    2172334554371520*a^3 +
    6517003663114560*a^2*b +
    6517003663114560*a^2*c +
    466605080611220628*a^2 +
    6517003663114560*a*b^2 +
    13034007326229120*a*b*c +
    933210161222441256*a*b +
    117083285913586608*a*c +
    4503125714534342280*a +
    26062031508373476*b^2 +
    52124063016746952*b*c +
    2767021532775411912*b +
    318640906848847968*c +
    9394628533146191412
def slope (a b : ℕ) : ℕ :=
    1217182482178678128960*a^2 +
    2434364964357356257920*a*b +
    71082875787150909119088*a +
    22998523110965911862472*b +
    205712195835453128007648
def intercept (a b : ℕ) : ℕ :=
    405727494059559376320*a^3 +
    1217182482178678128960*a^2*b +
    349057530327904908805428*a^2 +
    1217182482178678128960*a*b^2 +
    760229523732874813114056*a*b +
    3039582798376230600712680*a +
    11455516461675188783076*b^2 +
    2045376157248037821195912*b +
    5508253845234642078493812
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 8 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source11,source13,source14,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 840
def denominator : ℕ := 35423942400
def g0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    814775761050790*a +
    250145024267600*b +
    2064307829007340
def identitySlack0 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    38570882177225794760*a +
    12558280798330590400*b +
    97801209921064331360
def helperSlack0 (a b c : ℕ) : ℕ :=
    402963651680979721920*a^3 +
    1211654797421518820160*a^2*b +
    1214418639800098474560*a^2*c +
    337446944698264360790796*a^2 +
    1214418639800098474560*a*b^2 +
    2431601121978776603520*a*b*c +
    713702980490532752599992*a*b +
    71836388995310359936656*a*c +
    2910756083624320986414360*a +
    11765600447794994945676*b^2 +
    23308607264398487787672*b*c +
    1915239683121523709313720*b +
    207998043992781710264352*c +
    5243707658723829608320140
def g1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    7948427056675525*a +
    250145024267600*b +
    244853488767832*c +
    18277190813851690
def identitySlack1 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    394374591692201924300*a +
    12558280798330590400*b +
    12292624550100237728*c +
    905917486965769912760
def helperSlack1 (a b c : ℕ) : ℕ :=
    401654463185863043520*a^3 +
    1209036420431285463360*a^2*b +
    1213109451304981796160*a^2*c +
    337428249315779185747596*a^2 +
    1213109451304981796160*a*b^2 +
    2430291933483659925120*a*b*c +
    713680090856016925975992*a*b +
    71822642514446902855056*a*c +
    2910670270581545913755160*a +
    11761406195764343364876*b^2 +
    23304413012367836206872*b*c +
    1915193823634754677108920*b +
    207968805443805057483552*c +
    5243582684742416716508940
def g2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    7948427056675525*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    8873973310608160*b +
    792286735176776*c +
    29235640288451530
def identitySlack2 (a b c : ℕ) : ℕ :=
    483006335386910720*a^2 +
    966012670773821440*a*b +
    966012670773821440*a*c +
    394374591692201924300*a +
    483006335386910720*b^2 +
    966012670773821440*b*c +
    440840715824635931840*b +
    37441843122246795904*c +
    1449073106189088584120
def helperSlack2 (a b c : ℕ) : ℕ :=
    400927136244131555520*a^3 +
    1207581766547822487360*a^2*b +
    1212382124363250308160*a^2*c +
    337415977329734784643596*a^2 +
    1212382124363250308160*a*b^2 +
    2429564606541928437120*a*b*c +
    713665467179527593060792*a*b +
    71816217792203423623056*a*c +
    2910608005911226285979160*a +
    11759054505319411553676*b^2 +
    23302061321922904395672*b*c +
    1915163003056491301464120*b +
    207955846898797077555552*c +
    5243487296749416554963340
def conductor (a b c : ℕ) : ℕ :=
    2172334554371520*a^3 +
    6517003663114560*a^2*b +
    6517003663114560*a^2*c +
    443688916826628396*a^2 +
    6517003663114560*a*b^2 +
    13034007326229120*a*b*c +
    887377833653256792*a*b +
    118127791402978896*a*c +
    4273964076688419960*a +
    26229344278136076*b^2 +
    52458688556272152*b*c +
    2630193801146908920*b +
    322443674396075232*c +
    8914058344748804940
def slope (a b : ℕ) : ℕ :=
    1217182482178678128960*a^2 +
    2434364964357356257920*a*b +
    71864633528395366855056*a +
    23317504897319002990872*b +
    208057733303044449176352
def intercept (a b : ℕ) : ℕ :=
    405727494059559376320*a^3 +
    1217182482178678128960*a^2*b +
    337602143913402205094796*a^2 +
    1217182482178678128960*a*b^2 +
    713867077338591112107192*a*b +
    2911834212541616944695960*a +
    11774498080715510148876*b^2 +
    1915655073381370127203320*b +
    5245563149617530976432140
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 9 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source15,source16,source17,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 216
def denominator : ℕ := 2342317824
def g0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    203277314574048*a +
    62622155543886*b +
    514483472349276
def identitySlack0 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    9605131981586574432*a +
    3143882696925252744*b +
    24328622447600723904
def helperSlack0 (a b c : ℕ) : ℕ :=
    26616067935278678208*a^3 +
    80059811415658975296*a^2*b +
    80271419025481915968*a^2*c +
    23070314461696644284172*a^2 +
    80271419025481915968*a*b^2 +
    160754445660786772608*a*b*c +
    48466997245453537814904*a*b +
    4628225420104455715392*a*c +
    198636893551796424561144*a +
    759489050067757120152*b^2 +
    1500607708375654286064*b*c +
    129856439666162533188744*b +
    13369789822698916938144*c +
    357273757627492454991900
def g1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2113521629990296*a +
    62622155543886*b +
    60921304847532*c +
    4855958304081356
def identitySlack1 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    248403258198982656*a*c +
    104906835273454957664*a +
    3143882696925252744*b +
    3058493188565496528*c +
    240787519101655739824
def helperSlack1 (a b c : ℕ) : ℕ :=
    26529501185805657024*a^3 +
    79886677916712932928*a^2*b +
    80184852276008894784*a^2*c +
    23069225761313809119372*a^2 +
    80184852276008894784*a*b^2 +
    160667878911313751424*a*b*c +
    48465631210854798341496*a*b +
    4627316469124912838976*a*c +
    198632362385245686534648*a +
    759211715851852811544*b^2 +
    1500330374159749977456*b*c +
    129853812905840578226184*b +
    13367856498235970917536*c +
    357267521948887424956572
def g2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2113521629990296*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2329624160132607*b +
    198741712717104*c +
    7736777710425902
def identitySlack2 (a b c : ℕ) : ℕ :=
    124201629099491328*a^2 +
    248403258198982656*a*b +
    248403258198982656*a*c +
    104906835273454957664*a +
    124201629099491328*b^2 +
    248403258198982656*b*c +
    115756046696719539108*b +
    9377426625960557856*c +
    383615565040765176808
def helperSlack2 (a b c : ℕ) : ℕ :=
    26481408547209534144*a^3 +
    79790492639520687168*a^2*b +
    80136759637412771904*a^2*c +
    23068423926070429168908*a^2 +
    80136759637412771904*a*b^2 +
    160619786272717628544*a*b*c +
    48464677082255864001912*a*b +
    4626904475459785967424*a*c +
    198628327807962290324856*a +
    759059422496298422424*b^2 +
    1500178080804195588336*b*c +
    129851824858888859090568*b +
    13367042129341706270688*c +
    357261385637445331988124
def conductor (a b c : ℕ) : ℕ :=
    123659611492032*a^3 +
    370978834476096*a^2*b +
    370978834476096*a^2*c +
    25277951051490060*a^2 +
    370978834476096*a*b^2 +
    741957668952192*a*b*c +
    50555902102980120*a*b +
    6625135984686912*a*c +
    243505039652998200*a +
    1473921279535320*b^2 +
    2947842559070640*b*c +
    149772835903083624*b +
    17980537548204000*c +
    507796308110297052
def slope (a b : ℕ) : ℕ :=
    80483026635304856640*a^2 +
    160966053270609713280*a*b +
    4630389589110356288064*a +
    1501287417667812822768*b +
    13374361028957587094304
def intercept (a b : ℕ) : ℕ :=
    26827675545101618880*a^3 +
    80483026635304856640*a^2*b +
    23082400461496900812300*a^2 +
    80483026635304856640*a*b^2 +
    48479762954545952879736*a*b +
    198721012027312254500856*a +
    760168759359915656856*b^2 +
    129888791668388289147336*b +
    357418600539302743989660
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 10 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source18,source19,source20,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 360
def denominator : ℕ := 6506438400
def g0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330480254219016*a +
    100118132498925*b +
    833162190203370
def identitySlack0 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    15591093483996593664*a +
    5026330723976030700*b +
    39327231599932773480
def helperSlack0 (a b c : ℕ) : ℕ :=
    73933512566608474560*a^3 +
    222388336616000258880*a^2*b +
    222976135532175094080*a^2*c +
    66138239645959117457556*a^2 +
    222976135532175094080*a*b^2 +
    446540069980525023360*a*b*c +
    145957922984323676736072*a*b +
    12569379037680523345992*a*c +
    578513559460964012546760*a +
    2032876718586453469788*b^2 +
    4057383701176436194776*b*c +
    392952592094262884148168*b +
    36221125331493453589128*c +
    1050997569502270409124948
def g1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3635800107466956*a +
    100118132498925*b +
    99645673972160*c +
    8345270896870770
def identitySlack1 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    180531034197641287824*a +
    5026330723976030700*b +
    5002611416098320640*c +
    413964294112425709080
def helperSlack1 (a b c : ℕ) : ℕ :=
    73746485638734663360*a^3 +
    222014282760252636480*a^2*b +
    222789108604301282880*a^2*c +
    66136304120458114894356*a^2 +
    222789108604301282880*a*b^2 +
    446353043052651212160*a*b*c +
    145955368488751853702472*a*b +
    12567317288214000337992*a*c +
    578506948274611830636360*a +
    2032257748515632999388*b^2 +
    4056764731105615724376*b*c +
    392947918002807966847368*b +
    36216634457830108841928*c +
    1050989583323936736104148
def g2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3635800107466956*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4395796893621135*b +
    323676851433600*c +
    13805081612597430
def identitySlack2 (a b c : ℕ) : ℕ :=
    207002715165818880*a^2 +
    414005430331637760*a*b +
    414005430331637760*a*c +
    180531034197641287824*a +
    207002715165818880*b^2 +
    414005430331637760*b*c +
    218685912849725690340*b +
    15249535450557568800*c +
    685067612056413363720
def helperSlack2 (a b c : ℕ) : ℕ :=
    73479304313200647360*a^3 +
    221479920109184604480*a^2*b +
    222521927278767266880*a^2*c +
    66131733701642717095956*a^2 +
    222521927278767266880*a*b^2 +
    446085861727117196160*a*b*c +
    145949951995738931520072*a*b +
    12564859219679346174792*a*c +
    578483626674860528969160*a +
    2031411674318108615388*b^2 +
    4055918656908091340376*b*c +
    392936554906441043613768*b +
    36211644845386666837128*c +
    1050953870756740144251348
def conductor (a b c : ℕ) : ℕ :=
    334023088512960*a^3 +
    1002069265538880*a^2*b +
    1002069265538880*a^2*c +
    76256857624016916*a^2 +
    1002069265538880*a*b^2 +
    2004138531077760*a*b*c +
    152513715248033832*a*b +
    17593882226657352*a*c +
    737516844601697160*a +
    3940415502904188*b^2 +
    7880831005808376*b*c +
    452259353179401768*b +
    47499854115272328*c +
    1538994269403939348
def slope (a b : ℕ) : ℕ :=
    223563934448349929280*a^2 +
    447127868896699858560*a*b +
    12575346088031547045192*a +
    4059262876499358773976*b +
    36233680629932487709128
def intercept (a b : ℕ) : ℕ :=
    74521311482783309760*a^3 +
    223563934448349929280*a^2*b +
    66175365379256099115156*a^2 +
    223563934448349929280*a*b^2 +
    145996927892943580972872*a*b +
    578774738945364915852360*a +
    2034755893909376048988*b^2 +
    393052165829063627973768*b +
    1051448662591103768676948
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem cfg_eq : cfg = groups 11 := rfl
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq (f : FlagDegree) (a b c : ℕ) :
    graph cfg scale f a b c = f.zOnly*g0 a b c+f.yz*g1 a b c+f.all*g2 a b c := by
  norm_num [cfg,scale,source5,source21,source22,graph,first,normal,raw,MovingFiberThreeSources6811.weight,
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
  norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,g0,g1,g2,coeff,pairNumerator,conductor,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50204 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    fin_cases j
    · have h : full a b c = scale^2*helper (cfg 0) a b c+helperSlack0 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 1) a b c+helperSlack1 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
        <;> ring
      rw [h]
      exact Nat.le_add_right _ _
    · have h : full a b c = scale^2*helper (cfg 2) a b c+helperSlack2 a b c := by
        norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,helper,pairNumerator,helperSlack2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11


