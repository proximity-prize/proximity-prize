import ProximityPrize.SubmissionLower.HFreeDirArith6813

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G0
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source0,source0,source0]
def scale : ℕ := 18
def denominator : ℕ := 16262856
def gLo0 (b c : ℕ) : ℕ :=
    5325894189560*b +
    46601779286330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    267327932950774640*b +
    2214072097527991220
def helperSlackLo0 (b c : ℕ) : ℕ :=
    5369108854096845000*b^2 +
    10739820796146894096*b*c +
    849553038793137407040*b +
    100801944383871298248*c +
    2408781412846935815292
def gLo1 (b c : ℕ) : ℕ :=
    5325894189560*b +
    5325894189560*c +
    403308827936260
def identitySlackLo1 (b c : ℕ) : ℕ :=
    267327932950774640*b +
    267327932950774640*c +
    19993568085492520840
def helperSlackLo1 (b c : ℕ) : ℕ :=
    5369108854096845000*b^2 +
    10739820796146894096*b*c +
    849553038793137407040*b +
    100801944383871298248*c +
    2408781412846935815292
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    175359420678410*b +
    18099455723173*c +
    619371572560936
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10348074142531584*b^2 +
    20696148285063168*b*c +
    8701944671956066100*b +
    858461035780922842*c +
    30688551973176807184
def helperSlackLo2 (b c : ℕ) : ℕ :=
    5369108854096845000*b^2 +
    10739820796146894096*b*c +
    849553038793137407040*b +
    100801944383871298248*c +
    2408781412846935815292
def conductorLo (b c : ℕ) : ℕ :=
    13145239400040*b^2 +
    26290478800080*b*c +
    1052349104873808*b +
    167159584125396*c +
    3537380919343356
def slopeLo (b : ℕ) : ℕ :=
    10745030831994807408*b +
    100837546302888077328
def interceptLo (b : ℕ) : ℕ :=
    5374318889944758312*b^2 +
    849726172958603996052*b +
    2409517448608460214780
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    18821021238949*a +
    5635136553464*b +
    65113556588511
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    894679295279783386*a +
    282850044164572016*b +
    3093229202645641614
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184663312431158088*a^3 +
    555593025246678360*a^2*b +
    557196113199882456*a^2*c +
    159994695330735163740*a^2 +
    557196113199882456*a*b^2 +
    1115995314352969008*a*b*c +
    319917626555509571544*a*b +
    35960862322115435196*a*c +
    1671863342390723788920*a +
    5833172300013943200*b^2 +
    11669550775934294592*b*c +
    1168635672900481906368*b +
    135926211169868457132*c +
    3920648455042649947872
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    175771743830282*a +
    5635136553464*b +
    5635136553464*c +
    578771327829774
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    20696148285063168*a*c +
    8722640820241129268*a +
    282850044164572016*b +
    282850044164572016*c +
    28700686715571517116
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184663312431158088*a^3 +
    555593025246678360*a^2*b +
    557196113199882456*a^2*c +
    159994695330735163740*a^2 +
    557196113199882456*a*b^2 +
    1115995314352969008*a*b*c +
    319917626555509571544*a*b +
    35960862322115435196*a*c +
    1671863342390723788920*a +
    5833172300013943200*b^2 +
    11669550775934294592*b*c +
    1168635672900481906368*b +
    135926211169868457132*c +
    3920648455042649947872
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    175771743830282*a +
    206161575936*b^2 +
    412323151872*b*c +
    175771743830282*b +
    18511778875045*c +
    794937154815282
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    20696148285063168*a*c +
    8722640820241129268*a +
    10348074142531584*b^2 +
    20696148285063168*b*c +
    8722640820241129268*b +
    879157184065986010*c +
    39400844719275404868
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184663312431158088*a^3 +
    555593025246678360*a^2*b +
    557196113199882456*a^2*c +
    159994695330735163740*a^2 +
    557196113199882456*a*b^2 +
    1115995314352969008*a*b*c +
    319917626555509571544*a*b +
    35960862322115435196*a*c +
    1671863342390723788920*a +
    5833172300013943200*b^2 +
    11669550775934294592*b*c +
    1168635672900481906368*b +
    135926211169868457132*c +
    3920648455042649947872
def conductorHi (a b c : ℕ) : ℕ :=
    1065818793672*a^3 +
    3197456381016*a^2*b +
    3197456381016*a^2*c +
    181016578260180*a^2 +
    3197456381016*a*b^2 +
    6394912762032*a*b*c +
    362033156520360*a*b +
    66969982937556*a*c +
    2057090509405584*a +
    16342695781056*b^2 +
    32685391562112*b*c +
    1411184805013152*b +
    230932110681936*c +
    5414520669282432
def slopeHi (a b : ℕ) : ℕ :=
    558799201153086552*a^2 +
    1117598402306173104*a*b +
    35980767332906166684*a +
    11676363899735412000*b +
    135980115011722763604
def interceptHi (a b : ℕ) : ℕ :=
    186266400384362184*a^3 +
    558799201153086552*a^2*b +
    160064737713301586796*a^2 +
    558799201153086552*a*b^2 +
    319994482061877112008*a*b +
    1672431995549724425712*a +
    5839985423815060608*b^2 +
    1168882456396409627652*b +
    3921884704668561765192
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
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G0

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source1,source1,source1]
def scale : ℕ := 21
def denominator : ℕ := 22135554
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    47160143516040
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280263144052647200*b +
    2221255696345712160
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1582013194381128618528*b +
    119361423458475903378*c +
    4509245214872187954324
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    644606867985700
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280263144052647200*b +
    280263144052647200*c +
    32063596037077426600
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1582013194381128618528*b +
    119361423458475903378*c +
    4509245214872187954324
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    281533736183938*b +
    18297029134004*c +
    995416759837192
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12072753166286848*b^2 +
    24145506332573696*b*c +
    14014583916177864292*b +
    860040861432836936*c +
    49497066646663398448
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1582013194381128618528*b +
    119361423458475903378*c +
    4509245214872187954324
def conductorLo (b c : ℕ) : ℕ :=
    14743973011500*b^2 +
    29487946023000*b*c +
    1659351192741108*b +
    176752007477964*c +
    5643502798478544
def slopeLo (b : ℕ) : ℕ :=
    13297339725701468664*b +
    119411237788124578536
def interceptLo (b : ℕ) : ℕ :=
    6651215507146794540*b^2 +
    1582344997704320461170*b +
    4510720581076565814552
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19138855569076*a +
    5944381276688*b +
    65938214492220
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    902295497514840904*a +
    298372273802077472*b +
    3105441972004731240
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    298945925955879804630*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    597727262491996600152*a*b +
    43003124202678702252*a*c +
    3131578827933494143338*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    2178604121827696932900*b +
    161225939719033408950*c +
    7341875841328096196232
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    282014779861122*a +
    5944381276688*b +
    5944381276688*c +
    926260863253926
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    14038729422510437988*a +
    298372273802077472*b +
    298372273802077472*c +
    46084216237732042764
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    298945925955879804630*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    597727262491996600152*a*b +
    43003124202678702252*a*c +
    3131578827933494143338*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    2178604121827696932900*b +
    161225939719033408950*c +
    7341875841328096196232
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    282014779861122*a +
    240521838592*b^2 +
    481043677184*b*c +
    282014779861122*b +
    18778072811188*c +
    1277191017859722
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    14038729422510437988*a +
    12072753166286848*b^2 +
    24145506332573696*b*c +
    14038729422510437988*b +
    884186367765410632*c +
    63523723316007549588
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    298945925955879804630*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    597727262491996600152*a*b +
    43003124202678702252*a*c +
    3131578827933494143338*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    2178604121827696932900*b +
    161225939719033408950*c +
    7341875841328096196232
def conductorHi (a b c : ℕ) : ℕ :=
    1243455259284*a^3 +
    3730365777852*a^2*b +
    3730365777852*a^2*c +
    283515862782852*a^2 +
    3730365777852*a*b^2 +
    7460731555704*a*b*c +
    567031725565704*a*b +
    72831997144656*a*c +
    3267897185391552*a +
    18474338789352*b^2 +
    36948677578704*b*c +
    2222652552528960*b +
    245853638844768*c +
    8629127576346528
def slopeHi (a b : ℕ) : ℕ :=
    760587179841849276*a^2 +
    1521174359683698552*a*b +
    43031111140180904784*a +
    14564986268893143408*b +
    161301468089491375740
def interceptHi (a b : ℕ) : ℕ :=
    253529059947283092*a^3 +
    760587179841849276*a^2*b +
    299076646427104399056*a^2 +
    760587179841849276*a*b^2 +
    597867635197843756200*a*b +
    3132691320986701363008*a +
    7285038778742631912*b^2 +
    2179071752063350109790*b +
    7344335253011149592604
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
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G1

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source2,source2,source2]
def scale : ℕ := 21
def denominator : ℕ := 22135554
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    48233915486690
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280263144052647200*b +
    2275152606640518260
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1444900813759590635274*b +
    121988113382173069098*c +
    4114363838815955246514
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    588555971117770
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280263144052647200*b +
    280263144052647200*c +
    29250177319688548180
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1444900813759590635274*b +
    121988113382173069098*c +
    4114363838815955246514
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    256871401086805*b +
    18769487660769*c +
    907976976203092
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12072753166286848*b^2 +
    24145506332573696*b*c +
    12776682668312370490*b +
    883755444725279346*c +
    45108114146933383048
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6643836169217143818*b^2 +
    13289960387771817942*b*c +
    1444900813759590635274*b +
    121988113382173069098*c +
    4114363838815955246514
def conductorLo (b c : ℕ) : ℕ :=
    14743973011500*b^2 +
    29487946023000*b*c +
    1520257595561496*b +
    179416635776424*c +
    5156675208349902
def slopeLo (b : ℕ) : ℕ :=
    13297339725701468664*b +
    122038344409548777921
def interceptLo (b : ℕ) : ℕ :=
    6651215507146794540*b^2 +
    1445211282159158354268*b +
    4115732557212673749078
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19611314095841*a +
    5944381276688*b +
    67484444989635
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    926010080807283314*a +
    298372273802077472*b +
    3183053465591979750
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    272934460260347966442*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    545719847409023195520*a*b +
    43999440642063104412*a*c +
    2857287797685502562700*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    1989484326123185545014*b +
    164848946082114976830*c +
    6698714900719403745972
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    257352444763989*a +
    5944381276688*b +
    5944381276688*c +
    845547631288863
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    12800828174644944186*a +
    298372273802077472*b +
    298372273802077472*c +
    42032896272477670542
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    272934460260347966442*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    545719847409023195520*a*b +
    43999440642063104412*a*c +
    2857287797685502562700*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    1989484326123185545014*b +
    164848946082114976830*c +
    6698714900719403745972
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    257352444763989*a +
    240521838592*b^2 +
    481043677184*b*c +
    257352444763989*b +
    19250531337953*c +
    1165088899128489
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12072753166286848*a^2 +
    24145506332573696*a*b +
    24145506332573696*a*c +
    12800828174644944186*a +
    12072753166286848*b^2 +
    24145506332573696*b*c +
    12800828174644944186*b +
    907900951057853042*c +
    57896869568412040386
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251256163254372192*a^3 +
    756041386456027476*a^2*b +
    758314283148938376*a^2*c +
    272934460260347966442*a^2 +
    758314283148938376*a*b^2 +
    1518901462990787652*a*b*c +
    545719847409023195520*a*b +
    43999440642063104412*a*c +
    2857287797685502562700*a +
    7275386544120070290*b^2 +
    14555334034270581786*b*c +
    1989484326123185545014*b +
    164848946082114976830*c +
    6698714900719403745972
def conductorHi (a b c : ℕ) : ℕ :=
    1243455259284*a^3 +
    3730365777852*a^2*b +
    3730365777852*a^2*c +
    260333596586250*a^2 +
    3730365777852*a*b^2 +
    7460731555704*a*b*c +
    520667193172500*a*b +
    73720206577476*a*c +
    2989709991032328*a +
    18474338789352*b^2 +
    36948677578704*b*c +
    2037194422956144*b +
    249406476576048*c +
    7887295058055264
def slopeHi (a b : ℕ) : ℕ :=
    760587179841849276*a^2 +
    1521174359683698552*a*b +
    44027579106011501004*a +
    14564986268893143408*b +
    164925042676746171345
def interceptHi (a b : ℕ) : ℕ :=
    253529059947283092*a^3 +
    760587179841849276*a^2*b +
    273057422577527424996*a^2 +
    760587179841849276*a*b^2 +
    545852461960825215696*a*b +
    2858324657673590127810*a +
    7285038778742631912*b^2 +
    1989922863281169462384*b +
    6700999789683723265992
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
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G2

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3
open scoped BigOperators
open RCN095 MovingFiberProfile6811 MovingFiberArithmeticBase6811
open MovingFiberCatalog6811 HFreeDirArith6813
def cfg : Fin 3 → Params := ![source3,source3,source3]
def scale : ℕ := 18
def denominator : ℕ := 16262856
def gLo0 (b c : ℕ) : ℕ :=
    4569960546736*b +
    40915071143710
def identitySlackLo0 (b c : ℕ) : ℕ :=
    229384599682866784*b +
    1928633469017322940
def helperSlackLo0 (b c : ℕ) : ℕ :=
    4686272867924954928*b^2 +
    9374004100585116360*b*c +
    1338109811141080943376*b +
    88661335366635985872*c +
    3820467851092365458688
def gLo1 (b c : ℕ) : ℕ :=
    4569960546736*b +
    4569960546736*c +
    636429006066200
def identitySlackLo1 (b c : ℕ) : ℕ :=
    229384599682866784*b +
    229384599682866784*c +
    31694802306546729200
def helperSlackLo1 (b c : ℕ) : ℕ :=
    4686272867924954928*b^2 +
    9374004100585116360*b*c +
    1338109811141080943376*b +
    88661335366635985872*c +
    3820467851092365458688
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    278355379513180*b +
    16020638205407*c +
    984541550189936
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10348074142531584*b^2 +
    20696148285063168*b*c +
    13871723829708511480*b +
    754116869294176238*c +
    49017893830286833184
def helperSlackLo2 (b c : ℕ) : ℕ :=
    4686272867924954928*b^2 +
    9374004100585116360*b*c +
    1338109811141080943376*b +
    88661335366635985872*c +
    3820467851092365458688
def conductorLo (b c : ℕ) : ℕ :=
    12434671853784*b^2 +
    24869343707568*b*c +
    1630395803753064*b +
    152592949427148*c +
    5567650040883312
def slopeLo (b : ℕ) : ℕ :=
    9378535050563964048*b +
    88692378503309084808
def interceptLo (b : ℕ) : ℕ :=
    4690803817903802616*b^2 +
    1338341884196835178404*b +
    3821515483614517286640
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    16742203721183*a +
    4879202910640*b +
    57348030928125
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    790335128793036782*a +
    244906710896664160*b +
    2703446407648226730
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184863698425308600*a^3 +
    555993797234979384*a^2*b +
    557396499194032968*a^2*c +
    253100999304079971552*a^2 +
    557396499194032968*a*b^2 +
    1116195700347119520*a*b*c +
    506080397292438721680*a*b +
    32204969385711235236*a*c +
    2653658569563187692024*a +
    5150536699836203640*b^2 +
    10303934466366667368*b*c +
    1843354815213366291816*b +
    120029508830234794284*c +
    6221024016873192837072
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    278767702665052*a +
    4879202910640*b +
    4879202910640*c +
    914887464794484
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    20696148285063168*a*c +
    13892419977993574648*a +
    244906710896664160*b +
    244906710896664160*c +
    45571700094378170856
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184863698425308600*a^3 +
    555993797234979384*a^2*b +
    557396499194032968*a^2*c +
    253100999304079971552*a^2 +
    557396499194032968*a*b^2 +
    1116195700347119520*a*b*c +
    506080397292438721680*a*b +
    32204969385711235236*a*c +
    2653658569563187692024*a +
    5150536699836203640*b^2 +
    10303934466366667368*b*c +
    1843354815213366291816*b +
    120029508830234794284*c +
    6221024016873192837072
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    278767702665052*a +
    206161575936*b^2 +
    412323151872*b*c +
    278767702665052*b +
    16432961357279*c +
    1263103091279052
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10348074142531584*a^2 +
    20696148285063168*a*b +
    20696148285063168*a*c +
    13892419977993574648*a +
    10348074142531584*b^2 +
    20696148285063168*b*c +
    13892419977993574648*b +
    774813017579239406*c +
    62899965734137876248
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184863698425308600*a^3 +
    555993797234979384*a^2*b +
    557396499194032968*a^2*c +
    253100999304079971552*a^2 +
    557396499194032968*a*b^2 +
    1116195700347119520*a*b*c +
    506080397292438721680*a*b +
    32204969385711235236*a*c +
    2653658569563187692024*a +
    5150536699836203640*b^2 +
    10303934466366667368*b*c +
    1843354815213366291816*b +
    120029508830234794284*c +
    6221024016873192837072
def conductorHi (a b c : ℕ) : ℕ :=
    1065818793672*a^3 +
    3197456381016*a^2*b +
    3197456381016*a^2*c +
    277831406437560*a^2 +
    3197456381016*a*b^2 +
    6394912762032*a*b*c +
    555662812875120*a*b +
    63061861433148*a*c +
    3218868447534144*a +
    15632128234800*b^2 +
    31264256469600*b*c +
    2182861160247168*b +
    212457354479280*c +
    8509752900773568
def slopeHi (a b : ℕ) : ℕ :=
    558799201153086552*a^2 +
    1117598402306173104*a*b +
    32222369571320279412*a +
    10309868118304568640*b +
    120076549450557883812
def interceptHi (a b : ℕ) : ℕ :=
    186266400384362184*a^3 +
    558799201153086552*a^2*b +
    253191662418940295256*a^2 +
    558799201153086552*a*b^2 +
    506176994059236946656*a*b +
    2654442493819781265432*a +
    5156470351774104912*b^2 +
    1843680679632000644652*b +
    6222766313239036968312
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
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50194 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
end ProximityPrize.SubmissionLower.MovingFiberArithmetic6811.G3

