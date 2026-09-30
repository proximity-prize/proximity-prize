import ProximityPrize.SubmissionLower.MovingFiberArithmetic6815A
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 216
def denominator : ℕ := 2340918144
def gLo0 (b c : ℕ) : ℕ :=
    55123001676891*b +
    475020311572550
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2765741486136329034*b +
    22332606678363735700
def helperSlackLo0 (b c : ℕ) : ℕ :=
    677767242150697505598*b^2 +
    1340242490172386980044*b*c +
    158047503409715647252500*b +
    12455799148799497205316*c +
    439483069397991397207842
def gLo1 (b c : ℕ) : ℕ :=
    55123001676891*b +
    53705626096596*c +
    5991631187983990
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2765741486136329034*b +
    2694626083770607704*c +
    297621978356953938260
def helperSlackLo1 (b c : ℕ) : ℕ :=
    677517160429997666622*b^2 +
    1339992408451687141068*b*c +
    158046543396881855491860*b +
    12454090256686691809476*c +
    439484491836745490358306
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2825190268278957*b +
    188845957072176*c +
    9513062221596442
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124127410932154368*b^2 +
    248254821864308736*b*c +
    140550246573046478118*b +
    8874732076348403424*c +
    472504979535208176908
def helperSlackLo2 (b c : ℕ) : ℕ :=
    677364867074443277502*b^2 +
    1339840115096132751948*b*c +
    158043823541783258891220*b +
    12453275887792427162628*c +
    439474696483819652325666
def conductorLo (b c : ℕ) : ℕ :=
    1451643202179918*b^2 +
    2903286404359836*b*c +
    184628620425776868*b +
    17600977879243812*c +
    630015332286033666
def slopeLo (b : ℕ) : ℕ :=
    1340891740793434638924*b +
    12460226878643548201668
def interceptLo (b : ℕ) : ℕ :=
    678416492771745164478*b^2 +
    158086082877690579359508*b +
    439659811669917711124386
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    193725075047368*a +
    58833910043739*b +
    665034459378702
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    9119536941635686832*a +
    2951932602534560586*b +
    31265951556598650948
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26609655264958841184*a^3 +
    80030954876980239648*a^2*b +
    80232943959083955744*a^2*c +
    28586967199596657013122*a^2 +
    80232943959083955744*a*b^2 +
    160667877000271627584*a*b*c +
    59419456764360845417748*a*b +
    4521512652159015000900*a*c +
    302126749290588999591864*a +
    744594425729108789598*b^2 +
    1474098846411313264140*b*c +
    217346711733504945768456*b +
    16856861371304861588328*c +
    713022649214382255990456
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2621028002155232*a +
    58833910043739*b +
    57416534463444*c +
    8608948262898006
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    130306609032554699968*a +
    2951932602534560586*b +
    2880817200168839256*c +
    427742395326107866644
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26532707043205044576*a^3 +
    79877058433472646432*a^2*b +
    80155995737330159136*a^2*c +
    28586278047672549126018*a^2 +
    80155995737330159136*a*b^2 +
    160590928778517830976*a*b*c +
    59418440582494283895060*a*b +
    4520557211641059889476*a*c +
    302125514549727217063608*a +
    744267395786655154014*b^2 +
    1473771816468859628556*b*c +
    217344889435248100078344*b +
    16854273986895854877672*c +
    713023449115976920703160
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2621028002155232*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2830138146101421*b +
    193793834894640*c +
    12131616284840442
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    130306609032554699968*a +
    124127410932154368*b^2 +
    248254821864308736*b*c +
    140798501394910786854*b +
    9122986898212712160*c +
    602687461156830722508
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26484614404608921696*a^3 +
    79780873156280400672*a^2*b +
    80107903098734036256*a^2*c +
    28585065822342794699778*a^2 +
    80107903098734036256*a*b^2 +
    160542836139921708096*a*b*c +
    59417027971170378956820*a*b +
    4520049032698740772164*a*c +
    302117137430450506456248*a +
    744067009792504642014*b^2 +
    1473571430474709116556*b*c +
    217340853154102790785224*b +
    16852999531697867236392*c +
    713006440776465530366520
def conductorHi (a b c : ℕ) : ℕ :=
    123585717213792*a^3 +
    370757151641376*a^2*b +
    370757151641376*a^2*c +
    31472081785229058*a^2 +
    370757151641376*a*b^2 +
    741514303282752*a*b*c +
    62944163570458116*a*b +
    7268282721613764*a*c +
    364317723963659160*a +
    1822400353821294*b^2 +
    3644800707642588*b*c +
    247202026844593608*b +
    24498503449216200*c +
    962984560181677560
def slopeHi (a b : ℕ) : ℕ :=
    80434933041187671840*a^2 +
    160869866082375343680*a*b +
    4524005454183091729476*a +
    1474950086114464639116*b +
    16863579914090885597160
def interceptHi (a b : ℕ) : ℕ :=
    26811644347062557280*a^3 +
    80434933041187671840*a^2*b +
    28601907918366111569154*a^2 +
    80434933041187671840*a*b^2 +
    59435248722833451348756*a*b +
    302258007405507030455736*a +
    745445665432260164574*b^2 +
    217400679181788276374280*b +
    713315910871539249930936
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
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 378
def denominator : ℕ := 7169061816
def gLo0 (b c : ℕ) : ℕ :=
    97103071945692*b +
    862162941984460
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4872049531803150408*b +
    40631304190792867040
def helperSlackLo0 (b c : ℕ) : ℕ :=
    2087719876592441417178*b^2 +
    4191819108741119496744*b*c +
    468472780583227365146460*b +
    38768615579087371444788*c +
    1224863415895962505021614
def gLo1 (b c : ℕ) : ℕ :=
    97103071945692*b +
    97953497293869*c +
    9055043078043960
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4872049531803150408*b +
    4914718773222583206*c +
    449074012877106791040
def helperSlackLo1 (b c : ℕ) : ℕ :=
    2087263297104769475586*b^2 +
    4191362529253447555152*b*c +
    468471084283215855312408*b +
    38765414612580051192012*c +
    1224866289731444224407126
def gLo2 (b c : ℕ) : ℕ :=
    4329393094656*b^2 +
    8658786189312*b*c +
    5147547234039522*b +
    328496099063895*c +
    15475693921132356
def identitySlackLo2 (b c : ℕ) : ℕ :=
    217222969131270144*b^2 +
    434445938262540288*b*c +
    256171547512430633628*b +
    15431219570297696130*c +
    768071509149344347944
def helperSlackLo2 (b c : ℕ) : ℕ :=
    2086330500301998842226*b^2 +
    4190429732450676921792*b*c +
    468462417766499638455120*b +
    38759859560835732818736*c +
    1224846219651660217722582
def conductorLo (b c : ℕ) : ℕ :=
    4688875681284402*b^2 +
    9377751362568804*b*c +
    548265466157300388*b +
    57054071355952068*c +
    1866704348318179086
def slopeLo (b : ℕ) : ℕ :=
    4193827076595504702240*b +
    38782246688896656059568
def interceptLo (b : ℕ) : ℕ :=
    2089727844446826622674*b^2 +
    468580920981398923588884*b +
    1225354150284373696257702
def gHi0 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    352247720082314*a +
    103597161587676*b +
    1207916539394646
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    217222969131270144*a^2 +
    434445938262540288*a*b +
    16622933403275851036*a +
    5197883985500055624*b +
    56928401483117367804
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    81492086028893745240*a^3 +
    245094849650623866264*a^2*b +
    245713441214566496808*a^2*c +
    75597267763534079983374*a^2 +
    245713441214566496808*a*b^2 +
    492045473993075624160*a*b*c +
    173880581836034611999908*a*b +
    14060237442358442282424*a*c +
    819358611167060864082576*a +
    2292378176641197856770*b^2 +
    4601754300402575006472*b*c +
    641985101519671742877288*b +
    52459973530291636827588*c +
    1968624139850302202289288
def gHi1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3957106279299264*a +
    103597161587676*b +
    104447586935853*c +
    13005655234671096
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    217222969131270144*a^2 +
    434445938262540288*a*b +
    434445938262540288*a*c +
    196442363049292928736*a +
    5197883985500055624*b +
    5240553226919488422*c +
    645190539815448369504
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    81344802323193118920*a^3 +
    244800282239222613624*a^2*b +
    245566157508865870488*a^2*c +
    75595941319494057199398*a^2 +
    245566157508865870488*a*b^2 +
    491898190287374997840*a*b*c +
    173878651528801216648020*a*b +
    14058416033677328858280*a*c +
    819356226138335171405736*a +
    2291774313447825288858*b^2 +
    4601150437209202438560*b*c +
    641981769479838238943988*b +
    52455098438808903776988*c +
    1968625807817392551155616
def gHi2 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3957106279299264*a +
    4329393094656*b^2 +
    8658786189312*b*c +
    5156206020228834*b +
    337154885253207*c +
    19428470807336964
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    217222969131270144*a^2 +
    434445938262540288*a*b +
    434445938262540288*a*c +
    196442363049292928736*a +
    217222969131270144*b^2 +
    434445938262540288*b*c +
    256605993450693173916*b +
    15865665508560236418*c +
    964296649229506006536
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    81050234911791866280*a^3 +
    244211147416420108344*a^2*b +
    245271590097464617848*a^2*c +
    75591422837808470364726*a^2 +
    245271590097464617848*a*b^2 +
    491603622875973745200*a*b*c +
    173872905682901457927348*a*b +
    14055097240467643387896*a*c +
    819333241493766557658696*a +
    2290546949233653402858*b^2 +
    4599923072995030552560*b*c +
    641967946252045065871308*b +
    52446519161266301185968*c +
    1968586977007314116306064
def conductorHi (a b c : ℕ) : ℕ :=
    395261216261352*a^3 +
    1185783648784056*a^2*b +
    1185783648784056*a^2*c +
    93587686991555382*a^2 +
    1185783648784056*a*b^2 +
    2371567297568112*a*b*c +
    187175373983110764*a*b +
    23438242382661324*a*c +
    1080364032542438568*a +
    5874659330068458*b^2 +
    11749318660136916*b*c +
    734255056491627096*b +
    79306530089829336*c +
    2853875955085323624
def slopeHi (a b : ℕ) : ℕ :=
    246332032778509127352*a^2 +
    492664065557018254704*a*b +
    14067881467470890638776*a +
    4604380859820902842512*b +
    52480630073649427168176
def interceptHi (a b : ℕ) : ℕ :=
    82110677592836375784*a^3 +
    246332032778509127352*a^2*b +
    75639331803209305528134*a^2 +
    246332032778509127352*a*b^2 +
    173925272435128165380708*a*b +
    819724637764408551917904*a +
    2295004736059525692810*b^2 +
    642136695333808969439424*b +
    1969439455387949798446488
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
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 27
def denominator : ℕ := 36576846
def gLo0 (b c : ℕ) : ℕ :=
    7138415936163*b +
    60552249349760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    358162881181042362*b +
    2850515754565184740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
def gLo1 (b c : ℕ) : ℕ :=
    7138415936163*b +
    7138415936163*c +
    740894169953600
def identitySlackLo1 (b c : ℕ) : ℕ :=
    358162881181042362*b +
    358162881181042362*c +
    36798358474632579400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
def gLo2 (b c : ℕ) : ℕ :=
    309242363904*b^2 +
    618484727808*b*c +
    323324839032829*b +
    23511252928669*c +
    1142799052169204
def identitySlackLo2 (b c : ℕ) : ℕ :=
    15515926366519296*b^2 +
    31031852733038592*b*c +
    16072394230185423446*b +
    1104600482719169006*c +
    56738374097141178496
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10922297281651989468*b^2 +
    21849504020160666480*b*c +
    2338012944507203180946*b +
    196966484374269198726*c +
    6656751314498987215758
def conductorLo (b c : ℕ) : ℕ :=
    18910932470262*b^2 +
    37821864940524*b*c +
    1914569502273576*b +
    226933725637800*c +
    6490309702448178
def slopeLo (b : ℕ) : ℕ :=
    21865084031205868788*b +
    197071799760392489316
def interceptLo (b : ℕ) : ℕ :=
    10937877292697191776*b^2 +
    2338660699519149940662*b +
    6659602356867712889904
def gHi0 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    24593601202333*a +
    7602279482019*b +
    84681984646941
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    15515926366519296*a^2 +
    31031852733038592*a*b +
    1158906225001986542*a +
    381436770730821306*b +
    3986147971642074834
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
def gHi1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    323943323760637*a +
    7602279482019*b +
    7602279482019*c +
    1064373627809085
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    15515926366519296*a^2 +
    31031852733038592*a*b +
    31031852733038592*a*c +
    16103426082918462038*a +
    381436770730821306*b +
    381436770730821306*c +
    52878510549625944990
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
def gHi2 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    323943323760637*a +
    309242363904*b^2 +
    618484727808*b*c +
    323943323760637*b +
    24129737656477*c +
    1466433133565937
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    15515926366519296*a^2 +
    31031852733038592*a*b +
    31031852733038592*a*c +
    16103426082918462038*a +
    15515926366519296*b^2 +
    31031852733038592*b*c +
    16103426082918462038*b +
    1135632335452207598*c +
    72826284253693121238
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    414122346127579572*a^3 +
    1247176302242351004*a^2*b +
    1251985566101963292*a^2*c +
    441658568420872494192*a^2 +
    1251985566101963292*a*b^2 +
    2508780396063538872*a*b*c +
    883008130645279281744*a*b +
    71018836786852913088*a*c +
    4622937700376473437474*a +
    11964817841805942264*b^2 +
    23939354404328184360*b*c +
    3219145500636262507590*b +
    266104937381042544426*c +
    10838025632396552572404
def conductorHi (a b c : ℕ) : ℕ :=
    1598091170868*a^3 +
    4794273512604*a^2*b +
    4794273512604*a^2*c +
    328061859538806*a^2 +
    4794273512604*a*b^2 +
    9588547025208*a*b*c +
    656123719077612*a*b +
    93578460199020*a*c +
    3764148468011928*a +
    23705205982866*b^2 +
    47410411965732*b*c +
    2565898947838584*b +
    315717912324216*c +
    9927994402092168
def slopeHi (a b : ℕ) : ℕ :=
    1256794829961575580*a^2 +
    2513589659923151160*a*b +
    71078050854239731272*a +
    23959743679232998956*b +
    266264657570693040912
def interceptHi (a b : ℕ) : ℕ :=
    418931609987191860*a^3 +
    1256794829961575580*a^2*b +
    441915502368386371068*a^2 +
    1256794829961575580*a*b^2 +
    883285453867697973216*a*b +
    4625099883814868639820*a +
    11985207116710756860*b^2 +
    3220060960342908734202*b +
    10842786733520019184308
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
    norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    227123608966120*b +
    1962085248063300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11395699956266104880*b +
    92608200213360394200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10788159601498425061506*b^2 +
    21513302885187504249732*b*c +
    2123003999485637569676556*b +
    196405984272909192954288*c +
    5775658061067928159053366
def gLo1 (b c : ℕ) : ℕ :=
    227123608966120*b +
    225611741680472*c +
    19948839528421450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11395699956266104880*b +
    11319843527076002128*c +
    989238144453082592300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10784377501401421323906*b^2 +
    21509520785090500512132*b*c +
    2122970546028311346274956*b +
    196380006573609546997488*c +
    5775584890903728231942966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9983821590984960*b +
    748511705502288*c +
    32350456257847930
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    496258292487705287040*b +
    35220840302684750112*c +
    1604471886393372079820
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10782074299419271611906*b^2 +
    21507217583108350800132*b*c +
    2122948347161968733348556*b +
    196366357068099407264688*c +
    5775531339147457547315766
def conductorLo (b c : ℕ) : ℕ :=
    26093810124594306*b^2 +
    52187620249188612*b*c +
    2960971989623422956*b +
    317219339510597808*c +
    10073154870362318166
def slopeLo (b : ℕ) : ℕ :=
    21522200518108019452932*b +
    196465540239899281093488
def interceptLo (b : ℕ) : ℕ :=
    10797057234418940264706*b^2 +
    2123466459832360592156556*b +
    5777748893679478592080566
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    241554919281640*b +
    2744390349876990
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    37640470415771590220*a +
    12119776520037005360*b +
    129524590382573428260
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369802462594925355080742*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    793823106269087012118684*a*b +
    70803773427188919899448*a*c +
    3935504907308918744447544*a +
    11799109461508455794466*b^2 +
    23537966447586145370052*b*c +
    2915007950892128091407880*b +
    265387838995123042811976*c +
    9341357737923496157128488
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    241554919281640*b +
    240043051995992*c +
    28645297412075655
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    12119776520037005360*b +
    12043920090846902608*c +
    1420904250289174577970
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785154873864220923942*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    793800852724822103843484*a*b +
    70789275375337310497848*a*c +
    3935419098604909425829944*a +
    11794163638304681676066*b^2 +
    23533020624382371251652*b*c +
    2914954571336750500492680*b +
    265348526967078557834376*c +
    9341214903053241275176488
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    10003063338072320*b +
    767753452589648*c +
    41051724651674295
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    497223727906066487680*b +
    36186275721045950752*c +
    2036379354766842021330
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369773707198184844786342*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    793786374520218846505884*a*b +
    70781105068433675694648*a*c +
    3935359511252512594885944*a +
    11791133109380800476066*b^2 +
    23529990095458490051652*b*c +
    2914919348919688093204680*b +
    265327434481606514786376*c +
    9341112484293311404254888
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    505408450261226742*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    1010816900522453484*a*b +
    129566017151511768*a*c +
    5830429466544967944*a +
    32606919474309666*b^2 +
    65213838948619332*b*c +
    3965275780796161080*b +
    440272247312394216*c +
    15400346923095964488
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    70837497156568304027448*a +
    23549627922885240227652*b +
    265478354849113935424776
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    369983069739869648101542*a^2 +
    1216455140244462521760*a*b^2 +
    794015374889330399997084*a*b +
    3937068608183686383820344*a +
    11810770936807550652066*b^2 +
    2915657152174337342457480*b +
    9344834428107248516162088
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
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G7
