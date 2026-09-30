import ProximityPrize.SubmissionLower.MovingFiberArithmetic6815B
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    223343940752000*b +
    1957274690704500
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11206058883290848000*b +
    92366835308439963000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10628812564384132664706*b^2 +
    21353955800720917334532*b*c +
    2162637281768824290078156*b +
    196203663257892546483888*c +
    5826402928650630267414966
def gLo1 (b c : ℕ) : ℕ :=
    223343940752000*b +
    225611741680472*c +
    19944028971062650
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11206058883290848000*b +
    11319843527076002128*c +
    988996779548162161100
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10625078952749911026306*b^2 +
    21350222189086695696132*b*c +
    2162592448509129388066956*b +
    196177261284636042267888*c +
    5826271604277057136326966
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    10301313720971040*b +
    748511705502288*c +
    32754543075987130
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    512188142617626864960*b +
    35220840302684750112*c +
    1624746538406688300620
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10622727262304979215106*b^2 +
    21347870498641763884932*b*c +
    2162581629445155453750156*b +
    196164036053082760794288*c +
    5826276206730159655677366
def conductorLo (b c : ℕ) : ℕ :=
    26046457830075906*b^2 +
    52092915660151812*b*c +
    2984648136882622956*b +
    318450499168076208*c +
    10156494908714702166
def slopeLo (b : ℕ) : ℕ :=
    21362853433641432537732*b +
    196263219224882634623088
def interceptLo (b : ℕ) : ℕ :=
    10637710197304647867906*b^2 +
    2163099742115547312558156*b +
    5828493761262180700442166
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    237775251067520*b +
    2739579792518190
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    37640470415771590220*a +
    11930135447061748480*b +
    129283225477652997060
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    369806733557242919355942*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    807208406829668659293084*a*b +
    70803967854562993480248*a*c +
    3952577168197627026162744*a +
    11639762424394163397666*b^2 +
    23378619363119558454852*b*c +
    2968026533735896458983880*b +
    265185712407480469922376*c +
    9409170595432588982930088
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    237775251067520*b +
    240043051995992*c +
    28640486854716855
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    11930135447061748480*b +
    12043920090846902608*c +
    1420662885384254146770
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401557481262804138720*a^3 +
    1208600009273762451360*a^2*b +
    1212527574759112486560*a^2*c +
    369785158851456960469542*a^2 +
    1212527574759112486560*a*b^2 +
    2428982715003575008320*a*b*c +
    807181934789141708387484*a*b +
    70789275848860255681848*a*c +
    3952449854027207925849144*a +
    11634865089653171378466*b^2 +
    23373722028378566435652*b*c +
    2967957555881888146828680*b +
    265145782151627998288776*c +
    9408932367871275940034088
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8710889267370045*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    10320555468058400*b +
    767753452589648*c +
    41455811469813495
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    432390186082650541830*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    513153578035988065600*b +
    36186275721045950752*c +
    2056654006780158242130
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400830154321072650720*a^3 +
    1207145355390299475360*a^2*b +
    1211800247817380998560*a^2*c +
    369777978160502409061542*a^2 +
    1211800247817380998560*a*b^2 +
    2428255388061843520320*a*b*c +
    807171675080800493680284*a*b +
    70781299495807749275448*a*c +
    3952431772141220876601144*a +
    11631786072266508079266*b^2 +
    23370643010991903136452*b*c +
    2967937931763456460780680*b +
    265125307893963941896776*c +
    9408925341802404230056488
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    509386043000772342*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    1018772086001544684*a*b +
    130039540096695768*a*c +
    5878160579419515144*a +
    32559567179791266*b^2 +
    65119134359582532*b*c +
    3996907113534452280*b +
    441976929915056616*c +
    15527440481583350088
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    70837691583942377608248*a +
    23390280838418653312452*b +
    265276228261471362535176
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    369987340702187212376742*a^2 +
    1216455140244462521760*a*b^2 +
    807400675449912047171484*a*b +
    3954140869072394665535544*a +
    11651423899693258255266*b^2 +
    2968675735018105710033480*b +
    9412647285616341341963688
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
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 840
def denominator : ℕ := 35402774400
def gLo0 (b c : ℕ) : ℕ :=
    230903277180240*b +
    1996961420600300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11585341029241361760*b +
    94358077294231832200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10947603688046482638006*b^2 +
    21672747091596057325932*b*c +
    2012795416473151058045340*b +
    198547667234261671078512*c +
    5521658595317978282234310
def gLo1 (b c : ℕ) : ℕ :=
    230903277180240*b +
    225611741680472*c +
    19232075321503450
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11585341029241361760*b +
    11319843527076002128*c +
    953275217135178860300
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10943409436015831057206*b^2 +
    21668552839565405745132*b*c +
    2012762624668687268966940*b +
    198518428685285018297712*c +
    5521598959896139992650310
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9348837331012800*b +
    753803241002056*c +
    30820707857292730
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482717709180600320*b^2 +
    965435418361200640*b*c +
    464398592227862131200*b +
    35486337804850109744*c +
    1527718290143915475020
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10941057745570899246006*b^2 +
    21666201149120473933932*b*c +
    2012731270740725115638940*b +
    198505470140277038369712*c +
    5521500905171079990439110
def conductorLo (b c : ℕ) : ℕ :=
    26213670620094006*b^2 +
    52427341240188012*b*c +
    2823786946889748540*b +
    322250994326122992*c +
    9591808615839460710
def slopeLo (b : ℕ) : ℕ :=
    21681644724516572529132*b +
    198607356544524409990512
def interceptLo (b : ℕ) : ℕ :=
    10956501320966997841206*b^2 +
    2013241475597338035470940*b +
    5523667430374974831722310
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    809965324278950*a +
    245334587495760*b +
    2792495361163410
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    38304214171184989300*a +
    12309417593012262240*b +
    131938211218858265340
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402721204369574519520*a^3 +
    1210927455487303212960*a^2*b +
    1213691297865882867360*a^2*c +
    356409437379866047279206*a^2 +
    1213691297865882867360*a*b^2 +
    2430146438110345389120*a*b*c +
    753668055357067013763612*a*b +
    71585210393289432845256*a*c +
    3777248171616654000979512*a +
    11958553548056513370966*b^2 +
    23697410653994698446252*b*c +
    2764644316967621581421592*b +
    268310958922576033882008*c +
    8942494561696340844642936
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8393397137383965*a +
    245334587495760*b +
    240043051995992*c +
    27611041075171575
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    416460335952728963910*a +
    12309417593012262240*b +
    12043920090846902608*c +
    1369011472841349268050
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401412015874457841120*a^3 +
    1208309078497069856160*a^2*b +
    1212382109370766188960*a^2*c +
    356391566312944080626406*a^2 +
    1212382109370766188960*a*b^2 +
    2428837249615228710720*a*b*c +
    753644680849619278851612*a*b +
    71568845535435742406856*a*c +
    3777167371142417842502712*a +
    11953050107530745111766*b^2 +
    23691907213468930187052*b*c +
    2764590769032700290787992*b +
    268266664704240807341208*c +
    8942370687678693246556536
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8393397137383965*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9368079078100160*b +
    773044988089416*c +
    39204484121133015
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482717709180600320*a^2 +
    965435418361200640*a*b +
    965435418361200640*a*c +
    416460335952728963910*a +
    482717709180600320*b^2 +
    965435418361200640*b*c +
    465364027646223331840*b +
    36451773223211310384*c +
    1943695908387463838610
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400684688932726353120*a^3 +
    1206854424613606880160*a^2*b +
    1211654782429034700960*a^2*c +
    356376918398721085941606*a^2 +
    1211654782429034700960*a*b^2 +
    2428109922673497222720*a*b*c +
    753626953918009620867612*a*b +
    71560966159308800198856*a*c +
    3777076489543489662470712*a +
    11949971090144081812566*b^2 +
    23688828196082266887852*b*c +
    2764543142827011942451992*b +
    268246554110047616693208*c +
    8942195671941986327510136
def conductorHi (a b c : ℕ) : ℕ :=
    2171036449905120*a^3 +
    6513109349715360*a^2*b +
    6513109349715360*a^2*c +
    482464369475281206*a^2 +
    6513109349715360*a*b^2 +
    13026218699430720*a*b*c +
    964928738950562412*a*b +
    131083421429353896*a*c +
    5555100497113621512*a +
    32726779969809366*b^2 +
    65453559939618732*b*c +
    3782202576490595592*b +
    446821306405761528*c +
    14666615779927706136
def slopeHi (a b : ℕ) : ℕ :=
    1216455140244462521760*a^2 +
    2432910280488925043520*a*b +
    71618982611131599072456*a +
    23709072129293793303852*b +
    268401656608302359366808
def interceptHi (a b : ℕ) : ℕ :=
    405485046748154173920*a^3 +
    1216455140244462521760*a^2*b +
    356584080443888142098406*a^2 +
    1216455140244462521760*a*b^2 +
    753854359896388203440412*a*b +
    3778753725555138988464312*a +
    11970215023355608228566*b^2 +
    2765271152946372589215192*b +
    8945837071470178866450936
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
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 216
def denominator : ℕ := 2340918144
def gLo0 (b c : ℕ) : ℕ :=
    57674277721422*b +
    497165824473180
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2893749210394627428*b +
    23443735642639945320
def helperSlackLo0 (b c : ℕ) : ℕ :=
    705412122723948431916*b^2 +
    1392464875200549283512*b*c +
    137060163644446227076884*b +
    12745137084326426595312*c +
    378066895713808981002630
def gLo1 (b c : ℕ) : ℕ :=
    57674277721422*b +
    55973427025068*c +
    5137578772834220
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2893749210394627428*b +
    2808410727555761832*c +
    254770752479229378280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    705134788508044123308*b^2 +
    1392187540984644974904*b*c +
    137058524389053178783380*b +
    12743203759863480574704*c +
    378065597569894650561030
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2462909069955555*b +
    188845957072176*c +
    8194670757388502
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124127410932154368*b^2 +
    248254821864308736*b*c +
    122373149728368106170*b +
    8874732076348403424*c +
    406356006210038995348
def helperSlackLo2 (b c : ℕ) : ℕ :=
    704982495152489734188*b^2 +
    1392035247629090585784*b*c +
    137056448173767793627284*b +
    12742389390969215927856*c +
    378059020417374129624582
def conductorLo (b c : ℕ) : ℕ :=
    1473040520265420*b^2 +
    2946081040530840*b*c +
    161077009701160260*b +
    17969793063174000*c +
    547370721569020518
def slopeLo (b : ℕ) : ℕ :=
    1393144584492707820216*b +
    12749708290585096751472
def interceptLo (b : ℕ) : ℕ :=
    706091832016106968620*b^2 +
    137094949127439508220244*b +
    378223906017377532672774
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    202040345118432*a +
    61385186088270*b +
    695495242350396
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    9536747302181251968*a +
    3079940326792858980*b +
    32794290881420425704
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26600036737239616608*a^3 +
    80011717821541790496*a^2*b +
    80223325431364731168*a^2*c +
    24495889584749406296382*a^2 +
    80223325431364731168*a*b^2 +
    160658258472552403008*a*b*c +
    51402107863738154696940*a*b +
    4611631787521216786656*a*c +
    259193458038404538956232*a +
    772229687774640491340*b^2 +
    1526311612911756343032*b*c +
    188342042304668273321184*b +
    17236328060721711988656*c +
    612764252274334910641776
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2243817114386056*a +
    61385186088270*b +
    59684335391916*c +
    7377684959979060
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    111380429949624063344*a +
    3079940326792858980*b +
    2994601843953993384*c +
    365964990365452670040
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26513469987766595424*a^3 +
    79838584322595748128*a^2*b +
    80136758681891709984*a^2*c +
    24494900276593032176574*a^2 +
    80136758681891709984*a*b^2 +
    160571691723079381824*a*b*c +
    51400754654616403247340*a*b +
    4610549703042727867872*a*c +
    259189990926441501048264*a +
    771865786809263161548*b^2 +
    1525947711946379013240*b*c +
    188339222973652419620448*b +
    17233399218529750070448*c +
    612760389759864443390832
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2243817114386056*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2467856947778019*b +
    193793834894640*c +
    10436013932863326
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124127410932154368*a^2 +
    248254821864308736*a*b +
    248254821864308736*a*c +
    111380429949624063344*a +
    124127410932154368*b^2 +
    248254821864308736*b*c +
    122621404550232414906*b +
    9122986898212712160*c +
    517612308748730904324
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26465377349170472544*a^3 +
    79742399045403502368*a^2*b +
    80088666043295587104*a^2*c +
    24493922102104445548350*a^2 +
    80088666043295587104*a*b^2 +
    160523599084483258944*a*b*c +
    51399576094133666107116*a*b +
    4610041524100408750560*a*c +
    259183895803312596429384*a +
    771665400815112649548*b^2 +
    1525747325952228501240*b*c +
    188336064383161489569888*b +
    17232124763331762429168*c +
    612748647566065008340848
def conductorHi (a b c : ℕ) : ℕ :=
    123585717213792*a^3 +
    370757151641376*a^2*b +
    370757151641376*a^2*c +
    27532548452402622*a^2 +
    370757151641376*a*b^2 +
    741514303282752*a*b*c +
    55065096904805244*a*b +
    7362691358809824*a*c +
    317043323969741928*a +
    1843797671906796*b^2 +
    3687595343813592*b*c +
    215771349454324128*b +
    24961727270342448*c +
    837005082803573616
def slopeHi (a b : ℕ) : ℕ :=
    80434933041187671840*a^2 +
    160869866082375343680*a*b +
    4614219171746763240672*a +
    1527202929813737820408*b +
    17243275043596105658160
def interceptHi (a b : ℕ) : ℕ :=
    26811644347062557280*a^3 +
    80434933041187671840*a^2*b +
    24509495310038858907198*a^2 +
    80434933041187671840*a*b^2 +
    51416604905929588785132*a*b +
    259311011131709512366536*a +
    773121004676621968716*b^2 +
    188390901614633342671392*b +
    613025421553528806052080
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
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6815 MovingFiberArithmeticBase6815
open MovingFiberCatalog6815 HFreeDirArith6815
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 360
def denominator : ℕ := 6502550400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    804299443743210
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    37853149566242838540
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1882708954581030949278*b^2 +
    3757053275717680215756*b*c +
    418730590437659977232340*b +
    34486527131241078222468*c +
    1119334564007250804763650
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8862743329077330
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4609569143560548390*b +
    4585864009438641280*c +
    439675742344867995420
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882089984510210478878*b^2 +
    3756434305646859745356*b*c +
    418729737045366190856340*b +
    34482036257577733475268*c +
    1119345681353080905029250
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4708650447131595*b +
    307183925358720*c +
    14731795051764750
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234250410955077463530*b +
    14411937981296825280*c +
    731147410975291726500
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881243910312686094878*b^2 +
    3755588231449335361356*b*c +
    418718765823297607539540*b +
    34477046645134291470468*c +
    1119311928169290574142850
def conductorLo (b c : ℕ) : ℕ :=
    3938060860543278*b^2 +
    7876121721086556*b*c +
    493794310176693540*b +
    47471470009952868*c +
    1684392859911146850
def slopeLo (b : ℕ) : ℕ :=
    3758932451040602794956*b +
    34499082429680112342468
def interceptLo (b : ℕ) : ℕ :=
    1884588129903953528478*b^2 +
    418839568936501534933140*b +
    1119832680889670407157250
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    328418638459656*a +
    98056516739565*b +
    1126533203467506
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    15477368476423188144*a +
    4919887670890934310*b +
    53020197936998074044
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73888981466606811360*a^3 +
    222254743315995269280*a^2*b +
    222842542232170104480*a^2*c +
    70480173771798725379618*a^2 +
    222842542232170104480*a*b^2 +
    446272883380515044160*a*b*c +
    156125970423189310679316*a*b +
    12523457003250956983812*a*c +
    756455296475903196806136*a +
    2068313273533554743358*b^2 +
    4128849712538902639116*b*c +
    574522590879492829691976*b +
    46675426354219402151400*c +
    1805309098109859542342328
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3874125390125628*a +
    98056516739565*b +
    97584058212800*c +
    12730683840467598
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    192378950744860075272*a +
    4919887670890934310*b +
    4896182536769027200*c +
    631744372984060118052
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73701954538733000160*a^3 +
    221880689460247646880*a^2*b +
    222655515304296293280*a^2*c +
    70479066510077722938018*a^2 +
    222655515304296293280*a*b^2 +
    446085856452641232960*a*b*c +
    156124057164469613956116*a*b +
    12521021199928686353412*a*c +
    756457799278324576367736*a +
    2067507276534860461758*b^2 +
    4128043715540208357516*b*c +
    574520198282335094215176*b +
    46668686704161660585000*c +
    1805323638492904150799928
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3874125390125628*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4716896910169035*b +
    315430388396160*c +
    18601797210371658
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206879018220257280*a^2 +
    413758036440514560*a*b +
    413758036440514560*a*c +
    192378950744860075272*a +
    206879018220257280*b^2 +
    413758036440514560*b*c +
    234664168991517978090*b +
    14825696017737339840*c +
    923319482701931544492
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73434773213198984160*a^3 +
    221346326809179614880*a^2*b +
    222388333978762277280*a^2*c +
    70473837046379595526818*a^2 +
    222388333978762277280*a*b^2 +
    445818675127107216960*a*b*c +
    156117714445248428144916*a*b +
    12518028768742964158212*a*c +
    756425924668892844479736*a +
    2066394021011802061758*b^2 +
    4126930460017149957516*b*c +
    574503418703696393119176*b +
    46660971841858030401000*c +
    1805262972982054681420728
def conductorHi (a b c : ℕ) : ℕ :=
    333823489025760*a^3 +
    1001470467077280*a^2*b +
    1001470467077280*a^2*c +
    84180294890934498*a^2 +
    1001470467077280*a*b^2 +
    2002940934154560*a*b*c +
    168360589781868996*a*b +
    19586309726288772*a*c +
    974110601876431896*a +
    4939531327620558*b^2 +
    9879062655241116*b*c +
    661153429491485256*b +
    66056309269164360*c +
    2574656990385670008
def slopeHi (a b : ℕ) : ℕ :=
    223430341148344939680*a^2 +
    446860682296689879360*a*b +
    12530599651434330353412*a +
    4131316686778000053516*b +
    46694536501925634805800
def interceptHi (a b : ℕ) : ℕ :=
    74476780382781646560*a^3 +
    223430341148344939680*a^2*b +
    70522482817559840835618*a^2 +
    223430341148344939680*a*b^2 +
    156170746443189523549716*a*b +
    756825834988824058012536*a +
    2070780247772652157758*b^2 +
    574675169800502250592776*b +
    1806136032258355065321528
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
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50174 ≤ full a b c/denominator := by
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6815.G11
