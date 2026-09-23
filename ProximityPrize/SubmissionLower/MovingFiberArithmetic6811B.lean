import ProximityPrize.SubmissionLower.MovingFiberArithmetic6811A

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 216
def denominator : ℕ := 2341851264
def gLo0 (b c : ℕ) : ℕ :=
    55123001676891*b +
    475020311572550
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2766843946169866854*b +
    22342478175431893100
def helperSlackLo0 (b c : ℕ) : ℕ :=
    678037436344874842578*b^2 +
    1340776755498234779604*b*c +
    150588703196489238573852*b +
    12460762703774596168476*c +
    418132621384596661188870
def gLo1 (b c : ℕ) : ℕ :=
    55123001676891*b +
    53705626096596*c +
    5696129141661110
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2766843946169866854*b +
    2695700196292539624*c +
    282910123449256392140
def helperSlackLo1 (b c : ℕ) : ℕ :=
    677787354624175003602*b^2 +
    1340526673777534940628*b*c +
    150586967287424257832988*b +
    12459053811661790772636*c +
    418130164336110587475462
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2692523913963345*b +
    188845957072176*c +
    9048709611979682
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124176889710379008*b^2 +
    248353779420758016*b*c +
    133947992262563593650*b +
    8878657431824529504*c +
    449388713384346385508
def helperSlackLo2 (b c : ℕ) : ℕ :=
    677635061268620614482*b^2 +
    1340374380421980551508*b*c +
    150584388503062709797596*b +
    12458239442767526125788*c +
    418121074336647785790726
def conductorLo (b c : ℕ) : ℕ :=
    1452221845781058*b^2 +
    2904443691562116*b*c +
    174260425669944588*b +
    17607993854800572*c +
    593720199156105126
def slopeLo (b : ℕ) : ℕ :=
    1341426006119282438484*b +
    12465190433618647164828
def interceptLo (b : ℕ) : ℕ :=
    678686686965922501458*b^2 +
    150625131324728828192028*b +
    418298606964888090252678
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    193725075047368*a +
    58833910043739*b +
    665034459378702
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    9123559879471316752*a +
    2953109280735435366*b +
    31279771772957613948
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26620342730318215584*a^3 +
    80063017273058362848*a^2*b +
    80265006355162078944*a^2*c +
    27187630092839358919494*a^2 +
    80265006355162078944*a*b^2 +
    160732001792427873984*a*b*c +
    56594052373618260389052*a*b +
    4523314985740353468060*a*c +
    287334659394944628707880*a +
    744891338611315988658*b^2 +
    1474686549113220787860*b*c +
    207062459035934191884792*b +
    16863579166259538842328*c +
    678279448411986635493768
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2491007415589504*a +
    58833910043739*b +
    57416534463444*c +
    8183425630009398
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    248353779420758016*a*c +
    123833073143187018496*a +
    2953109280735435366*b +
    2881965530858108136*c +
    406556930310497814732
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26543394508564418976*a^3 +
    79909120829550769632*a^2*b +
    80188058133408282336*a^2*c +
    27186658796977048987974*a^2 +
    80188058133408282336*a*b^2 +
    160655053570674077376*a*b*c +
    56592754047813496821948*a*b +
    4522359545222398356636*a*c +
    287330673748256168900904*a +
    744564308668862353074*b^2 +
    1474359519170767152276*b*c +
    207059578697507955170040*b +
    16860991781850532131672*c +
    678273900064452658108296
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2491007415589504*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2697471791785809*b +
    193793834894640*c +
    11537243088657954
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124176889710379008*a^2 +
    248353779420758016*a*b +
    248353779420758016*a*c +
    123833073143187018496*a +
    124176889710379008*b^2 +
    248353779420758016*b*c +
    134196346041984351666*b +
    9127011211245287520*c +
    573097609637823024996
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26495301869968296096*a^3 +
    79812935552358523872*a^2*b +
    80139965494812159456*a^2*c +
    27185497870175273265606*a^2 +
    80139965494812159456*a*b^2 +
    160606960932077954496*a*b*c +
    56591392735017570587580*a*b +
    4521851366280079239324*a*c +
    287322796789338288959784*a +
    744363922674711841074*b^2 +
    1474159133176616640276*b*c +
    207055734785627673146040*b +
    16859717326652544490392*c +
    678258045940235156081928
def conductorHi (a b c : ℕ) : ℕ :=
    123634980065952*a^3 +
    370904940197856*a^2*b +
    370904940197856*a^2*c +
    29744328612027078*a^2 +
    370904940197856*a*b^2 +
    741809880395712*a*b*c +
    59488657224054156*a*b +
    7271179952339484*a*c +
    343579365497202120*a +
    1823126785978914*b^2 +
    3646253571957828*b*c +
    233378177953800888*b +
    24508268866942200*c +
    907678871021346120
def slopeHi (a b : ℕ) : ℕ :=
    80466995437265795040*a^2 +
    160933990874531590080*a*b +
    4525807787764430196636*a +
    1475537788816372162836*b +
    16870297709045562851160
def interceptHi (a b : ℕ) : ℕ :=
    26822331812421931680*a^3 +
    80466995437265795040*a^2*b +
    27201788505891049950918*a^2 +
    80466995437265795040*a*b^2 +
    56609062026373102795452*a*b +
    287458290032450248274472*a +
    745742578314467363634*b^2 +
    207113492838764416477176*b +
    678555108205814096808840
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
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 378
def denominator : ℕ := 7171919496
def gLo0 (b c : ℕ) : ℕ :=
    97103071945692*b +
    862162941984460
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4873991593242064248*b +
    40649196858596792440
def helperSlackLo0 (b c : ℕ) : ℕ :=
    2088552168320783639238*b^2 +
    4193490121413436158984*b*c +
    447962807868018173366148*b +
    38784064902077111095908*c +
    1173468900313931803717752
def gLo1 (b c : ℕ) : ℕ :=
    97103071945692*b +
    97953497293869*c +
    8694255695905560
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4873991593242064248*b +
    4916677843168460586*c +
    431147050697541293040
def helperSlackLo1 (b c : ℕ) : ℕ :=
    2088095588833111697646*b^2 +
    4193033541925764217392*b*c +
    447959599452311374417824*b +
    38780863935569790843132*c +
    1173464213558840446078368
def gLo2 (b c : ℕ) : ℕ :=
    4329393094656*b^2 +
    8658786189312*b*c +
    4904325584460900*b +
    328496099063895*c +
    14805347172955176
def identitySlackLo2 (b c : ℕ) : ℕ :=
    217309556993163264*b^2 +
    434619113986326528*b*c +
    244066750505333460360*b +
    15438049255864668510*c +
    734735716460429001744
def helperSlackLo2 (b c : ℕ) : ℕ :=
    2087162792030341064286*b^2 +
    4192100745122993584032*b*c +
    447950311883160432040620*b +
    38775308883825472469856*c +
    1173441038206903519325616
def conductorLo (b c : ℕ) : ℕ :=
    4690744727276862*b^2 +
    9381489454553724*b*c +
    520485696421671024*b +
    57076813840647708*c +
    1769454336774973752
def slopeLo (b : ℕ) : ℕ :=
    4195498089267821364480*b +
    38797696011886395710688
def interceptLo (b : ℕ) : ℕ :=
    2090560136175168844734*b^2 +
    448065574878997771447824*b +
    1173932767790213858044416
def gHi0 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    352247720082314*a +
    103597161587676*b +
    1207916539394646
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    217309556993163264*a^2 +
    434619113986326528*a*b +
    16630238121263191796*a +
    5199955928731809144*b +
    56953468986455191404
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    81524816398245535560*a^3 +
    245193040758679237224*a^2*b +
    245811632322621867768*a^2*c +
    72612851066397155342016*a^2 +
    245811632322621867768*a*b^2 +
    492241856209186366080*a*b*c +
    166320612701557890942672*a*b +
    14065842097939110078024*a*c +
    785857447070920653019488*a +
    2293292294371697650110*b^2 +
    4603588965079206811272*b*c +
    613915012383310373381100*b +
    52480880222186587615668*c +
    1886712876868926354977376
def gHi1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3798360214306224*a +
    103597161587676*b +
    104447586935853*c +
    12486121787539656
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    217309556993163264*a^2 +
    434619113986326528*a*b +
    434619113986326528*a*c +
    188553924715789653216*a +
    5199955928731809144*b +
    5242642178658205482*c +
    619375009419926153424
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    81377532692544909240*a^3 +
    244898473347277984584*a^2*b +
    245664348616921241448*a^2*c +
    72610974762311704332312*a^2 +
    245664348616921241448*a*b^2 +
    492094572503485739760*a*b*c +
    166318132534279067365056*a*b +
    14064020689257996653880*a*c +
    785849700902149463163768*a +
    2292688431178325082198*b^2 +
    4602985101885834243360*b*c +
    613909618367736152107800*b +
    52476005130703854565068*c +
    1886702172965443557865656
def gHi2 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3798360214306224*a +
    4329393094656*b^2 +
    8658786189312*b*c +
    4912984370650212*b +
    337154885253207*c +
    18599377994166744
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    217309556993163264*a^2 +
    434619113986326528*a*b +
    434619113986326528*a*c +
    188553924715789653216*a +
    217309556993163264*b^2 +
    434619113986326528*b*c +
    244501369619319786888*b +
    15872668369850995038*c +
    923072331619225491696
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    81082965281143656600*a^3 +
    244309338524475479304*a^2*b +
    245369781205519988808*a^2*c +
    72606230443855751429016*a^2 +
    245369781205519988808*a*b^2 +
    491800005092084487120*a*b*c +
    166312160851608942575760*a*b +
    14060701896048311183496*a*c +
    785824514344427130593568*a +
    2291461066964153196198*b^2 +
    4601757737671662357360*b*c +
    613894948250737887446580*b +
    52467425853161251974048*c +
    1886658260806828850193360
def conductorHi (a b c : ℕ) : ℕ :=
    395418772452312*a^3 +
    1186256317356936*a^2*b +
    1186256317356936*a^2*c +
    88958606346866808*a^2 +
    1186256317356936*a*b^2 +
    2372512634713872*a*b*c +
    177917212693733616*a*b +
    23447585166725844*a*c +
    1024798048737552000*a +
    5877001044633798*b^2 +
    11754002089267596*b*c +
    697216652798047704*b +
    79338142690016616*c +
    2705689197938111256
def slopeHi (a b : ℕ) : ℕ :=
    246430223886564498312*a^2 +
    492860447773128996624*a*b +
    14073486123051558434376*a +
    4606215524497534647312*b +
    52501536765544377956256
def interceptHi (a b : ℕ) : ℕ :=
    82143407962188166104*a^3 +
    246430223886564498312*a^2*b +
    72652961145928831971624*a^2 +
    246430223886564498312*a*b^2 +
    166363349340507895408320*a*b +
    786204422568015093052776*a +
    2295918853790025486150*b^2 +
    614059278850112090667336*b +
    1887484228354335115338264
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
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 27
def denominator : ℕ := 36591426
def gLo0 (b c : ℕ) : ℕ :=
    7138415936163*b +
    60552249349760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    358305649499765622*b +
    2851773185906768240
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10926653006425182228*b^2 +
    21858215469707052000*b*c +
    2232216214524188256582*b +
    197044980398332262946*c +
    6352005150389268188046
def gLo1 (b c : ℕ) : ℕ :=
    7138415936163*b +
    7138415936163*c +
    706962975681060
def identitySlackLo1 (b c : ℕ) : ℕ :=
    358305649499765622*b +
    358305649499765622*c +
    35110126765424955240
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10926653006425182228*b^2 +
    21858215469707052000*b*c +
    2232216214524188256582*b +
    197044980398332262946*c +
    6352005150389268188046
def gLo2 (b c : ℕ) : ℕ :=
    309242363904*b^2 +
    618484727808*b*c +
    308395149587055*b +
    23511252928669*c +
    1089866156329404
def identitySlackLo2 (b c : ℕ) : ℕ :=
    15522111213797376*b^2 +
    31044222427594752*b*c +
    15329517004008570510*b +
    1105089262319577706*c +
    54104464740877882776
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10926653006425182228*b^2 +
    21858215469707052000*b*c +
    2232216214524188256582*b +
    197044980398332262946*c +
    6352005150389268188046
def conductorLo (b c : ℕ) : ℕ :=
    18918470610522*b^2 +
    37836941221044*b*c +
    1831130420004720*b +
    227024184331800*c +
    6198188933339442
def slopeLo (b : ℕ) : ℕ :=
    21873795480752254308*b +
    197150295784455553536
def interceptLo (b : ℕ) : ℕ :=
    10942233017470384536*b^2 +
    2232842202710937610812*b +
    6354747358853988091464
def gHi0 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    24593601202333*a +
    7602279482019*b +
    84681984646941
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    15522111213797376*a^2 +
    31044222427594752*a*b +
    1159416651567868522*a +
    381588816320461686*b +
    3987906552231437274
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    414289337641107372*a^3 +
    1247677276782934404*a^2*b +
    1252486540642546692*a^2*c +
    421585372870720776576*a^2 +
    1252486540642546692*a*b^2 +
    2509782345144705672*a*b*c +
    842877570067166119680*a*b +
    71047151317656343008*a*c +
    4411254987255937471218*a +
    11969591045681464344*b^2 +
    23948900812079228520*b*c +
    3073217458613005055682*b +
    266210996473779673086*c +
    10341669950714538276012
def gHi1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    309013634314863*a +
    7602279482019*b +
    7602279482019*c +
    1015512744090771
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    15522111213797376*a^2 +
    31044222427594752*a*b +
    31044222427594752*a*c +
    15360561226436165262*a +
    381588816320461686*b +
    381588816320461686*c +
    50447404706617921014
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    414289337641107372*a^3 +
    1247677276782934404*a^2*b +
    1252486540642546692*a^2*c +
    421585372870720776576*a^2 +
    1252486540642546692*a*b^2 +
    2509782345144705672*a*b*c +
    842877570067166119680*a*b +
    71047151317656343008*a*c +
    4411254987255937471218*a +
    11969591045681464344*b^2 +
    23948900812079228520*b*c +
    3073217458613005055682*b +
    266210996473779673086*c +
    10341669950714538276012
def gHi2 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    309013634314863*a +
    309242363904*b^2 +
    618484727808*b*c +
    309013634314863*b +
    24129737656477*c +
    1398570548280363
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    15522111213797376*a^2 +
    31044222427594752*a*b +
    31044222427594752*a*c +
    15360561226436165262*a +
    15522111213797376*b^2 +
    31044222427594752*b*c +
    15360561226436165262*b +
    1136133484747172458*c +
    69449503856100250662
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    414289337641107372*a^3 +
    1247677276782934404*a^2*b +
    1252486540642546692*a^2*c +
    421585372870720776576*a^2 +
    1252486540642546692*a*b^2 +
    2509782345144705672*a*b*c +
    842877570067166119680*a*b +
    71047151317656343008*a*c +
    4411254987255937471218*a +
    11969591045681464344*b^2 +
    23948900812079228520*b*c +
    3073217458613005055682*b +
    266210996473779673086*c +
    10341669950714538276012
def conductorHi (a b c : ℕ) : ℕ :=
    1598728190508*a^3 +
    4796184571524*a^2*b +
    4796184571524*a^2*c +
    314158920165630*a^2 +
    4796184571524*a*b^2 +
    9592369143048*a*b*c +
    628317840331260*a*b +
    93615761773620*a*c +
    3597244397412696*a +
    23714655182046*b^2 +
    47429310364092*b*c +
    2454652075764456*b +
    315843761533896*c +
    9482873138777016
def slopeHi (a b : ℕ) : ℕ :=
    1257295804502158980*a^2 +
    2514591609004317960*a*b +
    71106365385043161192*a +
    23969290086984043116*b +
    266370716663430169572
def interceptHi (a b : ℕ) : ℕ :=
    419098601500719660*a^3 +
    1257295804502158980*a^2*b +
    421834391600118090948*a^2 +
    1257295804502158980*a*b^2 +
    843146978071468248648*a*b +
    4413339997416313082784*a +
    11989980320586278940*b^2 +
    3074103236276337314304*b +
    10346252959874096088912
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
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 840
def denominator : ℕ := 35416886400
def gLo0 (b c : ℕ) : ℕ :=
    227123608966120*b +
    1962085248063300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11400242428445427280*b +
    92648885049353296200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10792460180556984779886*b^2 +
    21521878643934224800092*b*c +
    2037950428453834061011644*b +
    196484252976002133384528*c +
    5548039565940784523285574
def gLo1 (b c : ℕ) : ℕ :=
    227123608966120*b +
    225611741680472*c +
    19182166341377350
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11400242428445427280*b +
    11324355761909611568*c +
    951157613555222737900
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10788678080459981042286*b^2 +
    21518096543837221062492*b*c +
    2037908841031743402293244*b +
    196458275276702487427728*c +
    5547925725866939276232774
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9560498751003520*b +
    748511705502288*c +
    31045000646618230
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482910126651473920*b^2 +
    965820253302947840*b*c +
    475210856794321895680*b +
    35236387789207450272*c +
    1539597474592170764620
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10786374878477831330286*b^2 +
    21515793341855071350492*b*c +
    2037885308717507974118844*b +
    196444625771192347694928*c +
    5547865506847630454645574
def conductorLo (b c : ℕ) : ℕ :=
    26104211452024686*b^2 +
    52208422904049372*b*c +
    2811746793807708444*b +
    317345787208413648*c +
    9550750988792815974
def slopeLo (b : ℕ) : ℕ :=
    21530776276854740003292*b +
    196543808942992221523728
def interceptLo (b : ℕ) : ℕ :=
    10801357813477499983086*b^2 +
    2038389820473320437589244*b +
    5550015057015048476741574
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    241554919281640*b +
    2744390349876990
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    37656982397894835220*a +
    12124607618422638160*b +
    129581498573015258460
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402882835910511321120*a^3 +
    1211412350110113617760*a^2*b +
    1214176192488693272160*a^2*c +
    355716315429576221619270*a^2 +
    1214176192488693272160*a*b^2 +
    2431116227355966198720*a*b*c +
    762057411516529593739740*a*b +
    70831996477902404404488*a*c +
    3782367882274211762026680*a +
    11803814119852059005646*b^2 +
    23547350364902952906012*b*c +
    2798187957765897927847224*b +
    265493603407060231230456*c +
    8974688364925393824626904
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8373553879259835*a +
    241554919281640*b +
    240043051995992*c +
    27541288836921345
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    415633345902019370790*a +
    12124607618422638160*b +
    12048720951886822448*c +
    1366066590583009235730
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401719112803740940320*a^3 +
    1209084903896572856160*a^2*b +
    1213012469381922891360*a^2*c +
    355696049905352210259270*a^2 +
    1213012469381922891360*a*b^2 +
    2429952504249195817920*a*b*c +
    762032200169101808261340*a*b +
    70817498426050795002888*a*c +
    3782253234954690153217080*a +
    11798868296648284887246*b^2 +
    23542404541699178787612*b*c +
    2798123486442593024412024*b +
    265454291379015746252856*c +
    8974478979333144209743704
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8373553879259835*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9579740498090880*b +
    767753452589648*c +
    39408933652334385
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482910126651473920*a^2 +
    965820253302947840*a*b +
    965820253302947840*a*c +
    415633345902019370790*a +
    482910126651473920*b^2 +
    965820253302947840*b*c +
    476176677047624843520*b +
    36202208042510398112*c +
    1954747910367538661490
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400991785862009452320*a^3 +
    1207630250013109880160*a^2*b +
    1212285142440191403360*a^2*c +
    355684117340711782409670*a^2 +
    1212285142440191403360*a*b^2 +
    2429225177307464329920*a*b*c +
    762017237075537499211740*a*b +
    70809328119147160199688*a*c +
    3782188919923815124801080*a +
    11795837767724403687246*b^2 +
    23539374012775297587612*b*c +
    2798086445688676750164024*b +
    265433198893543703204856*c +
    8974365650520659056102104
def conductorHi (a b c : ℕ) : ℕ :=
    2171901852882720*a^3 +
    6515705558648160*a^2*b +
    6515705558648160*a^2*c +
    480542333013851670*a^2 +
    6515705558648160*a*b^2 +
    13031411117296320*a*b*c +
    961084666027703340*a*b +
    129617663827938408*a*c +
    5531942596054886280*a +
    32619917010672846*b^2 +
    65239834021345692*b*c +
    3766315754276763624*b +
    440447745477703896*c +
    14604323153686733304
def slopeHi (a b : ℕ) : ℕ :=
    1216940034867272926560*a^2 +
    2433880069734545853120*a*b +
    70865720207281788532488*a +
    23559011840202047763612*b +
    265584119261051123843256
def interceptHi (a b : ℕ) : ℕ :=
    405646678289090975520*a^3 +
    1216940034867272926560*a^2*b +
    355888534086925488214470*a^2 +
    1216940034867272926560*a*b^2 +
    762241291649177955192540*a*b +
    3783849795441543153831480*a +
    11815475595151153863246*b^2 +
    2798805702233275506568824*b +
    8977976314352018482946904
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
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G7

