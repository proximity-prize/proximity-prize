import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811B

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 840
def denominator : ℕ := 35416886400
def gLo0 (b c : ℕ) : ℕ :=
    223343940752000*b +
    1957274690704500
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11210525762105888000*b +
    92407423933285689000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10633049644997819935086*b^2 +
    21362468061003890204892*b*c +
    2077121284908485442240444*b +
    196281851144112615106128*c +
    5598195488178021586594374
def gLo1 (b c : ℕ) : ℕ :=
    223343940752000*b +
    225611741680472*c +
    19177355784018550
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11210525762105888000*b +
    11324355761909611568*c +
    950916152439155130700
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10629316033363598296686*b^2 +
    21358734449369668566492*b*c +
    2077068451027732078757244*b +
    196255449170856110890128*c +
    5598024160607110614034374
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9874211212775480*b +
    748511705502288*c +
    31444276907398630
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482910126651473920*b^2 +
    965820253302947840*b*c +
    490957340100503655920*b +
    35236387789207450272*c +
    1559638747225782162220
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10626964342918666485486*b^2 +
    21356382758924736755292*b*c +
    2077056165172159355347644*b +
    196242223939302829416528*c +
    5598021429084867517954374
def conductorLo (b c : ℕ) : ℕ :=
    26056840282274286*b^2 +
    52113680564548572*b*c +
    2835148151664406044*b +
    318577437621924048*c +
    9633129452988761574
def slopeLo (b : ℕ) : ℕ :=
    21371365693924405408092*b +
    196341407111102703245328
def interceptLo (b : ℕ) : ℕ :=
    10641947277918335138286*b^2 +
    2077560676927971818818044*b +
    5600170979252285540050374
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    237775251067520*b +
    2739579792518190
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    37656982397894835220*a +
    11934890952083098880*b +
    129340037456947651260
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402882835910511321120*a^3 +
    1211412350110113617760*a^2*b +
    1214176192488693272160*a^2*c +
    355720537857645353532870*a^2 +
    1214176192488693272160*a*b^2 +
    2431116227355966198720*a*b*c +
    775288635365135711438940*a*b +
    70832190905465230305288*a*c +
    3799243631173668870817080*a +
    11644403584292894160846*b^2 +
    23387939781972618310812*b*c +
    2850590038069155426775224*b +
    265291396002733538852856*c +
    9041715813634018864812504
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8373553879259835*a +
    237775251067520*b +
    240043051995992*c +
    27536478279562545
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    415633345902019370790*a +
    11934890952083098880*b +
    12048720951886822448*c +
    1365825129466941628530
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401719112803740940320*a^3 +
    1209084903896572856160*a^2*b +
    1213012469381922891360*a^2*c +
    355696053837159299542470*a^2 +
    1213012469381922891360*a*b^2 +
    2429952504249195817920*a*b*c +
    775259254009908665429340*a*b +
    70817498899762492506888*a*c +
    3799087951148608798599480*a +
    11639506249551902141646*b^2 +
    23383042447231626291612*b*c +
    2850510150279388558044024*b +
    265251465746881067219256*c +
    9041412126335427103644504
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8373553879259835*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9893452959862840*b +
    767753452589648*c +
    39808209913114785
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    415633345902019370790*a +
    482910126651473920*b^2 +
    965820253302947840*b*c +
    491923160353806603760*b +
    36202208042510398112*c +
    1974789183001150059090
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400991785862009452320*a^3 +
    1207630250013109880160*a^2*b +
    1212285142440191403360*a^2*c +
    355688339768780914323270*a^2 +
    1212285142440191403360*a*b^2 +
    2429225177307464329920*a*b*c +
    775248460924143616910940*a*b +
    70809522546709986100488*a*c +
    3799064668823272233591480*a +
    11636427232165238842446*b^2 +
    23379963429844962992412*b*c +
    2850488525991934249092024*b +
    265230991489217010827256*c +
    9041393099229284096287704
def conductorHi (a b c : ℕ) : ℕ :=
    2171901852882720*a^3 +
    6515705558648160*a^2*b +
    6515705558648160*a^2*c +
    484474140103134870*a^2 +
    6515705558648160*a*b^2 +
    13031411117296320*a*b*c +
    968948280206269740*a*b +
    130091375525442408*a*c +
    5579124281126284680*a +
    32572545840922446*b^2 +
    65145091681844892*b*c +
    3797580726312027624*b +
    442153107588718296*c +
    14729951495864794104
def slopeHi (a b : ℕ) : ℕ :=
    1216940034867272926560*a^2 +
    2433880069734545853120*a*b +
    70865914634844614433288*a +
    23399601257271713168412*b +
    265381911856724431465656
def interceptHi (a b : ℕ) : ℕ :=
    405646678289090975520*a^3 +
    1216940034867272926560*a^2*b +
    355892756514994620128070*a^2 +
    1216940034867272926560*a*b^2 +
    775472515497784072891740*a*b +
    3800725544341000262621880*a +
    11656065059591989018446*b^2 +
    2851207782536533005496824*b +
    9045003763060643523132504
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
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 840
def denominator : ℕ := 35416886400
def gLo0 (b c : ℕ) : ℕ :=
    230903277180240*b +
    1996961420600300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11589959094784966560*b +
    94399459653675474200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10951967765578817503386*b^2 +
    21681386348864330954292*b*c +
    1941389241616742318533908*b +
    198626788552448103568272*c +
    5323192607011023158125698
def gLo1 (b c : ℕ) : ℕ :=
    230903277180240*b +
    225611741680472*c +
    18540566172404850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11589959094784966560*b +
    11324355761909611568*c +
    918953134673817072900
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10947773513548165922586*b^2 +
    21677192096833679373492*b*c +
    1941347382442005600297108*b +
    198597550003471450787472*c +
    5323087634638355169162498
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9008667191742000*b +
    753803241002056*c +
    29696248545902130
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482910126651473920*b^2 +
    965820253302947840*b*c +
    447512223508749160800*b +
    35501991122082805264*c +
    1471898211648826841220
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10945421823103234111386*b^2 +
    21674840406388747562292*b*c +
    1941316295184989117922708*b +
    198584591458463470859472*c +
    5322990913256878709428098
def conductorLo (b c : ℕ) : ℕ :=
    26224119725455386*b^2 +
    52448239450910772*b*c +
    2691292449217710708*b +
    322379447706091152*c +
    9127961699993516898
def slopeLo (b : ℕ) : ℕ :=
    21690283981784846157492*b +
    198686477862710842480272
def interceptLo (b : ℕ) : ℕ :=
    10960865398499332706586*b^2 +
    1941814232562782411649108*b +
    5325096101281643835114498
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    809965324278950*a +
    245334587495760*b +
    2792495361163410
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    38320990730083222700*a +
    12314324284762177440*b +
    131996081509525823940
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402882835910511321120*a^3 +
    1211412350110113617760*a^2*b +
    1214176192488693272160*a^2*c +
    343713928263555627214914*a^2 +
    1214176192488693272160*a*b^2 +
    2431116227355966198720*a*b*c +
    726788297700353301047028*a*b +
    71613744586895160518136*a*c +
    3641455533839926021516008*a +
    11963321704873891729146*b^2 +
    23706858069833059060212*b*c +
    2666357657112629892676776*b +
    268417887092498957527848*c +
    8620931444727367313360712
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8089133846147305*a +
    245334587495760*b +
    240043051995992*c +
    26615268634836315
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    401357166759969039970*a +
    12314324284762177440*b +
    12048720951886822448*c +
    1319585932559553239910
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401573647415394642720*a^3 +
    1208793973119880260960*a^2*b +
    1212867003993576593760*a^2*c +
    343692759973364662520514*a^2 +
    1212867003993576593760*a*b^2 +
    2429807038860849520320*a*b*c +
    726761625969636568093428*a*b +
    71597379729041470079736*a*c +
    3641342585399378929727208*a +
    11957818264348123469946*b^2 +
    23701354629307290801012*b*c +
    2666291744584166674843176*b +
    268373592874163730987048*c +
    8620733383015848080624712
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8089133846147305*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9027908938829360*b +
    773044988089416*c +
    37775761518505755
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    401357166759969039970*a +
    482910126651473920*b^2 +
    965820253302947840*b*c +
    448478043762052108640*b +
    36467811375385753104*c +
    1872772468282144407270
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400846320473663154720*a^3 +
    1207339319236417284960*a^2*b +
    1212139677051845105760*a^2*c +
    343678209031734001314114*a^2 +
    1212139677051845105760*a*b^2 +
    2429079711919118032320*a*b*c +
    726743996010619243587828*a*b +
    71589500352914527871736*a*c +
    3641252649275827817567208*a +
    11954739246961460170746*b^2 +
    23698275611920627501812*b*c +
    2666244482022016330939176*b +
    268353482279970540339048*c +
    8620560549125509438448712
def conductorHi (a b c : ℕ) : ℕ :=
    2171901852882720*a^3 +
    6515705558648160*a^2*b +
    6515705558648160*a^2*c +
    460386670066564914*a^2 +
    6515705558648160*a*b^2 +
    13031411117296320*a*b*c +
    920773340133129828*a*b +
    131135672962589976*a*c +
    5290074640687445208*a +
    32739825284103546*b^2 +
    65479650568207092*b*c +
    3605550083792192376*b +
    446999415110032968*c +
    13959821572467279912
def slopeHi (a b : ℕ) : ℕ :=
    1216940034867272926560*a^2 +
    2433880069734545853120*a*b +
    71647516804737326745336*a +
    23718519545132153917812*b +
    268508584778225283012648
def interceptHi (a b : ℕ) : ℕ :=
    405646678289090975520*a^3 +
    1216940034867272926560*a^2*b +
    343880910166924427096514*a^2 +
    1216940034867272926560*a*b^2 +
    726966941079021195786228*a*b +
    3642886391510477243144808*a +
    11974983180172986586746*b^2 +
    2666955763752580721222376*b +
    8624101578607548991751112
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
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 216
def denominator : ℕ := 2341851264
def gLo0 (b c : ℕ) : ℕ :=
    57674277721422*b +
    497165824473180
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2894902695949055868*b +
    23454050049966115320
def helperSlackLo0 (b c : ℕ) : ℕ :=
    705693338439167388276*b^2 +
    1393019958955978946952*b*c +
    131816783543505135451020*b +
    12750215901864292741392*c +
    363274561671768684115434
def gLo1 (b c : ℕ) : ℕ :=
    57674277721422*b +
    55973427025068*c +
    4934850624775500
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2894902695949055868*b +
    2809530196096263192*c +
    244698509572700083800
def helperSlackLo1 (b c : ℕ) : ℕ :=
    705416004223263079668*b^2 +
    1392742624740074638344*b*c +
    131814456561546410106252*b +
    12748282577401346720784*c +
    363269824888265635229802
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2367661430959731*b +
    188845957072176*c +
    7870716563888022
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124176889710379008*b^2 +
    248353779420758016*b*c +
    117641844790680192534*b +
    8878657431824529504*c +
    390260530328433603468
def helperSlackLo2 (b c : ℕ) : ℕ :=
    705263710867708690548*b^2 +
    1392590331384520249224*b*c +
    131812433247160647290124*b +
    12747468208507082073936*c +
    363263512239837559258218
def conductorLo (b c : ℕ) : ℕ :=
    1473627693112020*b^2 +
    2947255386224040*b*c +
    153327816324789084*b +
    17976956053194000*c +
    520242007974751242
def slopeLo (b : ℕ) : ℕ :=
    1393699668248137483656*b +
    12754787108122962897552
def interceptLo (b : ℕ) : ℕ :=
    706373047731325924980*b^2 +
    131849893804085742401100*b +
    363423195871220420648298
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    202040345118432*a +
    61385186088270*b +
    695495242350396
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    9540936545418303168*a +
    3081168030514624380*b +
    32808720313438822584
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26610724202598991008*a^3 +
    80043780217619913696*a^2*b +
    80255387827442854368*a^2*c +
    23537808607869889578738*a^2 +
    80255387827442854368*a*b^2 +
    160722383264708649408*a*b*c +
    49422085103891608490484*a*b +
    4613470043106894744096*a*c +
    249007517998230476431224*a +
    772537622177889309780*b^2 +
    1526920134043245730632*b*c +
    181118591350278875312544*b +
    17243197040243495915856*c +
    588744059168886256259856
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2154616944532824*a +
    61385186088270*b +
    59684335391916*c +
    7085756642067108
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    248353779420758016*a*c +
    106948289838968022576*a +
    3081168030514624380*b +
    2995795530661831704*c +
    351460533129722510472
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26524157453125969824*a^3 +
    79870646718673871328*a^2*b +
    80168821077969833184*a^2*c +
    23536569217477072730994*a^2 +
    80168821077969833184*a*b^2 +
    160635816515235628224*a*b*c +
    49420481812533414312948*a*b +
    4612387958628405825312*a*c +
    249001612581793217980536*a +
    772173721212511979988*b^2 +
    1526556233077868400840*b*c +
    181114834210460901832608*b +
    17240268198051533997648*c +
    588734569792589292750096
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2154616944532824*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2372609308782195*b +
    193793834894640*c +
    10022859569509614
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    248353779420758016*a*c +
    106948289838968022576*a +
    124176889710379008*b^2 +
    248353779420758016*b*c +
    117890198570100950550*b +
    9127011211245287520*c +
    497084643277691247036
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26476064814529846944*a^3 +
    79774461441481625568*a^2*b +
    80120728439373710304*a^2*c +
    23535610279757400724722*a^2 +
    80120728439373710304*a*b^2 +
    160587723876639505344*a*b*c +
    49419322488819591794676*a*b +
    4611879779686086708000*a*c +
    248995705016811115810296*a +
    771973335218361467988*b^2 +
    1526355847083717888840*b*c +
    181111747757638508743968*b +
    17238993742853546356368*c +
    588723260424260190491664
def conductorHi (a b c : ℕ) : ℕ :=
    123634980065952*a^3 +
    370904940197856*a^2*b +
    370904940197856*a^2*c +
    26241289822947186*a^2 +
    370904940197856*a*b^2 +
    741809880395712*a*b*c +
    52482579645894372*a*b +
    7365626222029344*a*c +
    301542900028243416*a +
    1844532633309876*b^2 +
    3689065266619752*b*c +
    205439491030485600*b +
    24971677335025488*c +
    795667253160113424
def slopeHi (a b : ℕ) : ℕ :=
    80466995437265795040*a^2 +
    160933990874531590080*a*b +
    4616057427332441198112*a +
    1527811450945227208008*b +
    17250144023117889585360
def interceptHi (a b : ℕ) : ℕ :=
    26822331812421931680*a^3 +
    80466995437265795040*a^2*b +
    23550805160997829472754*a^2 +
    80466995437265795040*a*b^2 +
    49435972973921529861876*a*b +
    249119131666641038573688*a +
    773428939079870787156*b^2 +
    181165166265669757752672*b +
    588991522091230437981840
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
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 360
def denominator : ℕ := 6505142400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    804299443743210
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    37869854039845546740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883459493971719567218*b^2 +
    3758550952797664743636*b*c +
    400151527537453727950620*b +
    34500269427583974534108*c +
    1070726896549727474368230
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8489070683291130
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4611406576949778090*b +
    4587691993657335680*c +
    421098109398312707220
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882840523900899096818*b^2 +
    3757931982726844273236*b*c +
    400148004554276970027420*b +
    34495778553920629786908*c +
    1070724665921978066224230
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4487539856605575*b +
    307183925358720*c +
    14076704800488750
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223246653770939322750*b +
    14418329053695137280*c +
    698562425956796029500
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881994449703374712818*b^2 +
    3757085908529319889236*b*c +
    400136763918800509937820*b +
    34490788941477187782108*c +
    1070689565663185912931430
def conductorLo (b c : ℕ) : ℕ :=
    3939630622117218*b^2 +
    7879261244234436*b*c +
    465216710137171020*b +
    47490392746832508*c +
    1584353765761693830
def slopeLo (b : ℕ) : ℕ :=
    3760430128120587322836*b +
    34512824726023008654108
def interceptLo (b : ℕ) : ℕ :=
    1885338669294642146418*b^2 +
    400254015769011887691420*b +
    1071192562113026685049830
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    328418638459656*a +
    98056516739565*b +
    1126533203467506
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    15484184243083518864*a +
    4921848801225725610*b +
    53043594479686405764
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73918668866607920160*a^3 +
    222343805515998595680*a^2*b +
    222931604432173430880*a^2*c +
    67534597118347118713638*a^2 +
    222931604432173430880*a*b^2 +
    446451007780521696960*a*b*c +
    149219095795798380280956*a*b +
    12528448971254890564572*a*c +
    724096280481147207038376*a +
    2069138031490779295698*b^2 +
    4130495826751959035796*b*c +
    549036519758568752093496*b +
    46694027025239334125400*c +
    1727287991310711910337928
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3709709822811408*a +
    98056516739565*b +
    97584058212800*c +
    12192595627367178
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    184204253054674904352*a +
    4921848801225725610*b +
    4898134217933283200*c +
    604991918649744951732
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73731641938734108960*a^3 +
    221969751660250973280*a^2*b +
    222744577504299619680*a^2*c +
    67532519096695750019238*a^2 +
    222744577504299619680*a*b^2 +
    446263980852647885760*a*b*c +
    149216211777148317304956*a*b +
    12526013167932619934172*a*c +
    724089318366784834391976*a +
    2068332034492085014098*b^2 +
    4129689829753264754196*b*c +
    549030486810597678816696*b +
    46687287375181592559000*c +
    1727280689563323624430728
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3709709822811408*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4495786319643015*b +
    315430388396160*c +
    17782291391781438
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206961482850631680*a^2 +
    413922965701263360*a*b +
    413922965701263360*a*c +
    184204253054674904352*a +
    206961482850631680*b^2 +
    413922965701263360*b*c +
    223660576736640586110*b +
    14832252019396400640*c +
    882559717528620302172
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73464460613200092960*a^3 +
    221435389009182941280*a^2*b +
    222477396178765603680*a^2*c +
    67527191664919794428838*a^2 +
    222477396178765603680*a*b^2 +
    445996799527113869760*a*b*c +
    149209771089849303314556*a*b +
    12523020736746897738972*a*c +
    724056488564746282295976*a +
    2067218778969026614098*b^2 +
    4128576574230206354196*b*c +
    549013339850473272768696*b +
    46679572512877962375000*c +
    1727217819752943340616328
def conductorHi (a b c : ℕ) : ℕ :=
    333956555350560*a^3 +
    1001869666051680*a^2*b +
    1001869666051680*a^2*c +
    79418111438682918*a^2 +
    1001869666051680*a*b^2 +
    2003739332103360*a*b*c +
    158836222877365836*a*b +
    19594117080586332*a*c +
    916950029286334536*a +
    4941500288168898*b^2 +
    9883000576337796*b*c +
    623051063348485176*b +
    66082640161367160*c +
    2422219640164696008
def slopeHi (a b : ℕ) : ℕ :=
    223519403348348266080*a^2 +
    447038806696696532160*a*b +
    12535591619438263934172*a +
    4132962800991056450196*b +
    46713137172945566779800
def interceptHi (a b : ℕ) : ℕ :=
    74506467782782755360*a^3 +
    223519403348348266080*a^2*b +
    67574546065901308249638*a^2 +
    223519403348348266080*a*b^2 +
    149261511717591667231356*a*b +
    724443808045101721540776*a +
    2071605005729876710098*b^2 +
    549180248314087849114296*b +
    1728061823289327620821128
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
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G11

