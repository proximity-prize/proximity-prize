import ProximityPrize.SubmissionLower.ContactMovingFixedProfile6732Research
namespace ProximityPrize.SubmissionLower.ContactKernelArithmetic6733Research
open scoped BigOperators
open ContactFlagBezout6543Research
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
def n : Nat := 262144
def w : Nat := 131071
def errors : Nat := 80092
def agreements : Nat := n - errors
def gap : Nat := agreements - w
def u : Nat := n - w
def prime : Nat := 2130706433
def budget : Nat := prime^6 / 2^128 - 1000000000
structure Cap where
  total : Nat
  middle : Nat
  inner : Nat
  deriving DecidableEq,Repr
def normalize (p : Cap) : Cap :=
  let middle := min p.total p.middle
  let inner := min middle p.inner
  ⟨p.total,middle,inner⟩
def sub (p q : Cap) : Cap :=
  normalize ⟨p.total-q.total,p.middle-q.middle,p.inner-q.inner⟩
def CapLE (p q : Cap) : Prop :=
  p.total ≤ q.total ∧ p.middle ≤ q.middle ∧ p.inner ≤ q.inner
theorem sub_le_left (p q : Cap) : CapLE (sub p q) p := by
  simp [CapLE,sub,normalize]
theorem normalize_mono {p q : Cap} (h : CapLE p q) :
    CapLE (normalize p) (normalize q) := by
  rcases h with ⟨hL,hy,hs⟩
  simp only [CapLE,normalize]
  exact ⟨hL,min_le_min hL hy,min_le_min (min_le_min hL hy) hs⟩
theorem sub_antitone_right {p g h : Cap} (hgh : CapLE g h) :
    CapLE (sub p h) (sub p g) := by
  apply normalize_mono
  rcases hgh with ⟨hL,hy,hs⟩
  exact ⟨Nat.sub_le_sub_left hL p.total,
    Nat.sub_le_sub_left hy p.middle,
    Nat.sub_le_sub_left hs p.inner⟩
theorem le_sub_of_add_le {q g p : Cap}
    (hqMiddle : q.middle ≤ q.total) (hqInner : q.inner ≤ q.middle)
    (hTotal : q.total + g.total ≤ p.total)
    (hMiddle : q.middle + g.middle ≤ p.middle)
    (hInner : q.inner + g.inner ≤ p.inner) :
    CapLE q (sub p g) := by
  simp only [CapLE,sub,normalize]
  constructor
  · omega
  constructor
  · apply le_min
    · omega
    · omega
  · apply le_min
    · apply le_min
      · omega
      · omega
    · omega
def residualPadded (lhs rhs : Cap) (leftY : Nat) : Nat :=
  let cy := lhs.inner*rhs.total+lhs.total*rhs.inner
  let cr := leftY*rhs.total+lhs.total*rhs.middle
  let cz := leftY*rhs.inner+lhs.inner*rhs.middle
  let ay := max (1+2*w*leftY) (1+2*w*rhs.middle)
  let ar := max (w*(2*lhs.inner-1)) (w*(2*rhs.inner-1))
  let az := max (2*w*lhs.total+1) (2*w*rhs.total+1)
  (u*(ay*cy+ar*cr+az*cz)+(errors+1)*gap*cz)/gap
theorem residualPadded_mono {p q p' q' : Cap} {leftY : Nat}
    (hpL : p.total ≤ p'.total) (hps : p.inner ≤ p'.inner)
    (hqL : q.total ≤ q'.total) (hqy : q.middle ≤ q'.middle)
    (hqs : q.inner ≤ q'.inner) :
    residualPadded p q leftY ≤ residualPadded p' q' leftY := by
  have hcy : p.inner*q.total+p.total*q.inner ≤
      p'.inner*q'.total+p'.total*q'.inner := by gcongr
  have hcr : leftY*q.total+p.total*q.middle ≤
      leftY*q'.total+p'.total*q'.middle := by gcongr
  have hcz : leftY*q.inner+p.inner*q.middle ≤
      leftY*q'.inner+p'.inner*q'.middle := by gcongr
  have hay : max (1+2*w*leftY) (1+2*w*q.middle) ≤
      max (1+2*w*leftY) (1+2*w*q'.middle) := by
    exact max_le_max (le_refl _) (by gcongr)
  have har : max (w*(2*p.inner-1)) (w*(2*q.inner-1)) ≤
      max (w*(2*p'.inner-1)) (w*(2*q'.inner-1)) := by
    apply max_le_max <;> gcongr
  have haz : max (2*w*p.total+1) (2*w*q.total+1) ≤
      max (2*w*p'.total+1) (2*w*q'.total+1) := by
    apply max_le_max <;> gcongr
  unfold residualPadded
  dsimp only
  gcongr
def singular (p : Cap) (D : Nat) : Nat :=
  if p.inner = 0 ∨ p.total = 0 ∨ p.middle = 0 then 0 else
    let k := 2*p.inner-1
    let sy := (k*D-1)/w
    let sz := k*p.total
    (u*((1+2*w*sy)*sz+w*(2*sy*sz)+(2*w*sz+1)*sy)+
      (errors+1)*gap*sy+2*sz*sz*gap)/gap+1
theorem singular_mono {p q : Cap} {D : Nat}
    (hL : p.total ≤ q.total) (hm : p.middle ≤ q.middle)
    (hs : p.inner ≤ q.inner) : singular p D ≤ singular q D := by
  by_cases hp0 : p.inner = 0 ∨ p.total = 0 ∨ p.middle = 0
  · simp [singular,hp0]
  have hpi : 0 < p.inner := by omega
  have hpL : 0 < p.total := by omega
  have hpm : 0 < p.middle := by omega
  have hq0 : ¬(q.inner = 0 ∨ q.total = 0 ∨ q.middle = 0) := by omega
  simp only [singular,hp0,hq0,if_false]
  have hk : 2*p.inner-1 ≤ 2*q.inner-1 :=
    Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hs) 1
  have hsy : ((2*p.inner-1)*D-1)/w ≤ ((2*q.inner-1)*D-1)/w := by
    apply Nat.div_le_div_right
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right D hk) 1
  have hsz : (2*p.inner-1)*p.total ≤ (2*q.inner-1)*q.total :=
    Nat.mul_le_mul hk hL
  gcongr
def ensurePositiveSlope (p : Cap) : Cap :=
  ⟨p.total,max 1 p.middle,max 1 p.inner⟩
def singularPadded (p : Cap) (D : Nat) : Nat :=
  singular (ensurePositiveSlope p) D
theorem singularPadded_mono {p q : Cap} {D : Nat}
    (hL : p.total ≤ q.total) (hm : p.middle ≤ q.middle)
    (hs : p.inner ≤ q.inner) :
    singularPadded p D ≤ singularPadded q D := by
  exact singular_mono (p := ensurePositiveSlope p) (q := ensurePositiveSlope q)
    hL (max_le_max (le_refl 1) hm) (max_le_max (le_refl 1) hs)
def fixedProfile6733 : ContactRobustFixedMeet6656Research.Profile :=
  ⟨262144,131071,182052,41*182052,1240,11⟩
def flagOfCap (g : Cap) : ContactFlagBezout6543Research.FlagDegree :=
  ⟨g.total-g.middle,g.middle-g.inner,g.inner⟩
def properLedger (p : ContactRobustFixedMeet6656Research.Profile)
    (a b s : Nat) (flag : ContactFlagBezout6543Research.FlagDegree) : Nat :=
  (p.w+1)*ContactMovingReducedFactorLedger6720Research.factorDegreeCost
      p (ContactMovingAgreementCertificate6719Research.support a b s) a b s flag+
    ContactMovingReducedFactorLedger6720Research.factorUnitCost
      p (ContactMovingAgreementCertificate6719Research.support a b s) a b s flag
theorem sum_properLedger_le {J : Type*} [Fintype J]
    (p : ContactRobustFixedMeet6656Research.Profile) (a b s : Nat)
    (flags : J → ContactFlagBezout6543Research.FlagDegree)
    (cap : ContactFlagBezout6543Research.FlagDegree)
    (hi : (∑ j,(flags j).all) ≤ cap.all)
    (hm : (∑ j,((flags j).yz+(flags j).all)) ≤ cap.yz+cap.all)
    (ht : (∑ j,((flags j).zOnly+(flags j).yz+(flags j).all)) ≤
      cap.zOnly+cap.yz+cap.all) :
    (∑ j,properLedger p a b s (flags j)) ≤ properLedger p a b s cap := by
  simp only [properLedger,
    ContactMovingReducedFactorLedger6720Research.factorDegreeCost,
    ContactMovingReducedFactorLedger6720Research.factorUnitCost,
    Finset.sum_add_distrib,← Finset.mul_sum]
  gcongr
  all_goals first
    | exact ContactMovingReducedPositiveLedger6720Research.sum_degreeSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_unitSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s) a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_zSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s)
    | exact ContactMovingReducedPositiveLedger6720Research.sum_yzSlope_le
        flags cap hi hm ht (ContactMovingAgreementCertificate6719Research.support a b s)
    | exact ContactMovingReducedPositiveLedger6720Research.sum_degreeBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_unitBase_le
        flags cap hi hm ht a b s
    | exact ContactMovingReducedPositiveLedger6720Research.sum_zBase_le flags cap hi hm ht
    | exact ContactMovingReducedPositiveLedger6720Research.sum_yzBase_le flags cap hi hm ht
theorem identityDegree_linear6733
    (flag : ContactFlagBezout6543Research.FlagDegree) :
    ContactMovingFixedProfile6732Research.identityDegree
      fixedProfile6733 1186 42 9 flag =
      2752533 * flag.zOnly + 5505066 * flag.yz + 338692634 * flag.all := by
  open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
    ContactMovingPositiveLedger6719Research
    ContactMovingFixedProfile6732Research
    ContactMovingOuterBudget6719Research in
    rcases flag with ⟨z,y,t⟩
    norm_num [fixedProfile6733,identityDegree,paddedCut,centreFlag,directionFlag,
      flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
      nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
theorem properLedger_linear6733
    (flag : ContactFlagBezout6543Research.FlagDegree) :
    properLedger fixedProfile6733 1186 42 9 flag =
      3687067205837887497*flag.zOnly+
      94939662182135103155*flag.yz+
      486105150500085117845*flag.all := by
  open ContactFlagBezout6543Research ContactRobustFixedMeet6656Research
    ContactMovingPositiveLedger6719Research
    ContactMovingReducedPositiveLedger6720Research
    ContactMovingFixedProfile6732Research in
    rcases flag with ⟨z,y,t⟩
    norm_num [fixedProfile6733,properLedger,
      ContactMovingReducedFactorLedger6720Research.factorDegreeCost,
      ContactMovingReducedFactorLedger6720Research.factorUnitCost,
      ContactMovingReducedPositiveLedger6720Research.degreeSlope,
      ContactMovingReducedPositiveLedger6720Research.degreeBase,
      ContactMovingReducedPositiveLedger6720Research.unitSlope,
      ContactMovingReducedPositiveLedger6720Research.unitBase,
      ContactMovingReducedPositiveLedger6720Research.zSlope,
      ContactMovingReducedPositiveLedger6720Research.zBase,
      ContactMovingReducedPositiveLedger6720Research.yzSlope,
      ContactMovingReducedPositiveLedger6720Research.yzBase,
      ContactMovingReducedPositiveLedger6720Research.cutBase,
      ContactReducedTaylorProfileResearch.reducedAgreementDirection,
      ContactMovingAgreementCertificate6719Research.support,
      Profile.errors,Profile.gap,Profile.degreeIncidence,Profile.unitIncidence,
      centreFlag,directionFlag,surfaceFlag,normalFlag,fiberFlag,
      weightedMixed,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,
      add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
theorem identity_le_proper6733
    (flag : ContactFlagBezout6543Research.FlagDegree) :
    (fixedProfile6733.n - fixedProfile6733.w) *
        (fixedProfile6733.errors + 1) *
      ContactMovingFixedProfile6732Research.identityDegree
        fixedProfile6733 1186 42 9 flag ≤
      properLedger fixedProfile6733 1186 42 9 flag := by
  rw [identityDegree_linear6733,properLedger_linear6733]
  norm_num [fixedProfile6733,ContactRobustFixedMeet6656Research.Profile.errors]
  omega
def fixed (p : Cap) : Nat :=
  (3687067205837887497*p.total+
    91252594976297215658*p.middle+
    391165488317950014690*p.inner)/50981+1
theorem fixed_mono {p q : Cap}
    (hL : p.total ≤ q.total) (hy : p.middle ≤ q.middle)
    (hs : p.inner ≤ q.inner) : fixed p ≤ fixed q := by
  unfold fixed
  gcongr
theorem fixed_eq_proper_ceiling (g : Cap)
    (hm : g.middle ≤ g.total) (hi : g.inner ≤ g.middle) :
    fixed g =
      properLedger fixedProfile6733 1186 42 9 (flagOfCap g) /
          fixedProfile6733.gap + 1 := by
  have hnum :
      3687067205837887497*g.total+
          91252594976297215658*g.middle+
          391165488317950014690*g.inner =
        3687067205837887497*(g.total-g.middle)+
          94939662182135103155*(g.middle-g.inner)+
          486105150500085117845*g.inner := by
    omega
  rw [properLedger_linear6733]
  simpa [fixed,fixedProfile6733,
    ContactRobustFixedMeet6656Research.Profile.gap,flagOfCap] using
      congrArg (fun x : Nat => x/50981+1) hnum
theorem fixed_covers_identity_and_proper (g : Cap)
    (hm : g.middle ≤ g.total) (hi : g.inner ≤ g.middle) :
    properLedger fixedProfile6733 1186 42 9 (flagOfCap g) /
          fixedProfile6733.gap + 1 ≤ fixed g ∧
      ((fixedProfile6733.n-fixedProfile6733.w)*(fixedProfile6733.errors+1)*
          ContactMovingFixedProfile6732Research.identityDegree
            fixedProfile6733 1186 42 9 (flagOfCap g)) /
          fixedProfile6733.gap + 1 ≤ fixed g := by
  constructor
  · exact (fixed_eq_proper_ceiling g hm hi).ge
  · rw [fixed_eq_proper_ceiling g hm hi]
    gcongr
    exact identity_le_proper6733 (flagOfCap g)
def parentA : Cap := ⟨1003041,56,12⟩
def parentB : Cap := ⟨1242,112,25⟩
def parentC : Cap := ⟨624668,59,11⟩
def hmax : Cap := ⟨1240,54,12⟩
def stage1Padded (g : Cap) : Nat :=
  residualPadded (sub parentB g) (sub parentA g) 112+
    singularPadded (sub parentB g) (81*agreements)
def stage2Padded (g : Cap) : Nat :=
  residualPadded (sub hmax g) (sub parentC g) 56+
    singularPadded (sub hmax g) (41*agreements)
def coupledPadded (g : Cap) : Nat :=
  stage1Padded g+stage2Padded g+fixed g+singularPadded g (41*agreements)
def actualLedgerPadded (qA qB qH qC g : Cap) : Nat :=
  residualPadded qB qA 112+singularPadded qB (81*agreements)+
    residualPadded qH qC 56+singularPadded qH (41*agreements)+
    fixed g+singularPadded g (41*agreements)
theorem actualLedgerPadded_le_coupled {qA qB qH qC g : Cap}
    (hA : CapLE qA (sub parentA g))
    (hB : CapLE qB (sub parentB g))
    (hH : CapLE qH (sub hmax g))
    (hC : CapLE qC (sub parentC g)) :
    actualLedgerPadded qA qB qH qC g ≤ coupledPadded g := by
  rcases hA with ⟨hAL,hAy,hAs⟩
  rcases hB with ⟨hBL,hBy,hBs⟩
  rcases hH with ⟨hHL,hHy,hHs⟩
  rcases hC with ⟨hCL,hCy,hCs⟩
  have hr1 := residualPadded_mono hBL hBs hAL hAy hAs (leftY := 112)
  have hs1 := singularPadded_mono hBL hBy hBs (D := 81*agreements)
  have hr2 := residualPadded_mono hHL hHs hCL hCy hCs (leftY := 56)
  have hs2 := singularPadded_mono hHL hHy hHs (D := 41*agreements)
  unfold actualLedgerPadded coupledPadded stage1Padded stage2Padded
  omega
theorem stagesPadded_antitone {g h : Cap} (hgh : CapLE g h) :
    stage1Padded h + stage2Padded h ≤
      stage1Padded g + stage2Padded g := by
  have ha := sub_antitone_right (p := parentA) hgh
  have hb := sub_antitone_right (p := parentB) hgh
  have hh := sub_antitone_right (p := hmax) hgh
  have hc := sub_antitone_right (p := parentC) hgh
  rcases ha with ⟨haL,haY,haS⟩
  rcases hb with ⟨hbL,hbY,hbS⟩
  rcases hh with ⟨hhL,hhY,hhS⟩
  rcases hc with ⟨hcL,hcY,hcS⟩
  exact Nat.add_le_add
    (Nat.add_le_add
      (residualPadded_mono hbL hbS haL haY haS)
      (singularPadded_mono hbL hbY hbS))
    (Nat.add_le_add
      (residualPadded_mono hhL hhS hcL hcY hcS)
      (singularPadded_mono hhL hhY hhS))
theorem coupledPadded_box {lo g hi : Cap}
    (hlo : CapLE lo g) (hhi : CapLE g hi) :
    coupledPadded g ≤
      stage1Padded lo+stage2Padded lo+fixed hi+singularPadded hi (41*agreements) := by
  rcases hhi with ⟨hL,hY,hS⟩
  have hst := stagesPadded_antitone hlo
  have hf := fixed_mono hL hY hS
  have hs := singularPadded_mono hL hY hS (D := 41*agreements)
  unfold coupledPadded
  omega
def stagesPaddedMax : Nat := 7486606599893923
theorem stagesPadded_le_max (g : Cap) :
    stage1Padded g+stage2Padded g ≤ stagesPaddedMax := by
  have ha := sub_le_left parentA g
  have hb := sub_le_left parentB g
  have hh := sub_le_left hmax g
  have hc := sub_le_left parentC g
  rcases ha with ⟨haL,haY,haS⟩
  rcases hb with ⟨hbL,hbY,hbS⟩
  rcases hh with ⟨hhL,hhY,hhS⟩
  rcases hc with ⟨hcL,hcY,hcS⟩
  calc
    stage1Padded g+stage2Padded g ≤
        (residualPadded parentB parentA 112+singularPadded parentB (81*agreements))+
        (residualPadded hmax parentC 56+singularPadded hmax (41*agreements)) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (residualPadded_mono hbL hbS haL haY haS)
          (singularPadded_mono hbL hbY hbS))
        (Nat.add_le_add
          (residualPadded_mono hhL hhS hcL hcY hcS)
          (singularPadded_mono hhL hhY hhS))
    _ = stagesPaddedMax := by
      norm_num [stagesPaddedMax,residualPadded,singularPadded,
        ensurePositiveSlope,singular,parentA,parentB,
        parentC,hmax,agreements,errors,gap,u,w,n]
def paddedExceptionCap (g : Cap) : Nat :=
  if g.inner ≤ 10 then 1240
  else if g.middle ≤ 53 then 0
  else if g.total ≤ 1206 then 1186
  else 33
theorem casePadded_s10 {g : Cap}
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 10) :
    coupledPadded g+1240 ≤ 270601956763892927 := by
  have hf := fixed_mono (p := g) (q := ⟨1240,54,10⟩) hL hy hs
  have hsing := singularPadded_mono (p := g) (q := ⟨1240,54,10⟩)
    hL hy hs (D := 41*agreements)
  have hstage := stagesPadded_le_max g
  calc
    coupledPadded g+1240 ≤
        (stagesPaddedMax+fixed ⟨1240,54,10⟩+
          singularPadded ⟨1240,54,10⟩ (41*agreements))+1240 := by
      unfold coupledPadded
      omega
    _ = 270601956763892927 := by
      norm_num [stagesPaddedMax,fixed,singularPadded,ensurePositiveSlope,
        singular,agreements,errors,gap,u,w,n]
theorem casePadded_y53 {g : Cap}
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 53)
    (hs11 : g.inner = 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    coupledPadded g ≤ 271853757876760953 := by
  have hlo : CapLE ⟨11,11,11⟩ g := by
    simp only [CapLE]
    omega
  have hhi : CapLE g ⟨1240,53,11⟩ := by
    simp only [CapLE]
    omega
  have h := coupledPadded_box hlo hhi
  norm_num [stage1Padded,stage2Padded,residualPadded,parentA,parentB,
    parentC,hmax,sub,normalize,fixed,singularPadded,ensurePositiveSlope,
    singular,agreements,errors,
    gap,u,w,n] at h ⊢
  exact h
theorem casePadded_y54_low {g : Cap}
    (hloL : 54 ≤ g.total) (hhiL : g.total ≤ 1206)
    (hy54 : g.middle = 54) (hs11 : g.inner = 11) :
    coupledPadded g + 1186 ≤ 270712739758543224 := by
  have hlo : CapLE ⟨54,54,11⟩ g := by
    simp only [CapLE]
    omega
  have hhi : CapLE g ⟨1206,54,11⟩ := by
    simp only [CapLE]
    omega
  have h := coupledPadded_box hlo hhi
  norm_num [stage1Padded,stage2Padded,residualPadded,parentA,parentB,
    parentC,hmax,sub,normalize,fixed,singularPadded,ensurePositiveSlope,
    singular,agreements,errors,
    gap,u,w,n] at h ⊢
  omega
theorem casePadded_y54_high {g : Cap}
    (hloL : 1207 ≤ g.total) (hhiL : g.total ≤ 1240)
    (hy54 : g.middle = 54) (hs11 : g.inner = 11) :
    coupledPadded g + 33 ≤ 272979521442990893 := by
  have hlo : CapLE ⟨1207,54,11⟩ g := by
    simp only [CapLE]
    omega
  have hhi : CapLE g ⟨1240,54,11⟩ := by
    simp only [CapLE]
    omega
  have h := coupledPadded_box hlo hhi
  norm_num [stage1Padded,stage2Padded,residualPadded,parentA,parentB,
    parentC,hmax,sub,normalize,fixed,singularPadded,ensurePositiveSlope,
    singular,agreements,errors,
    gap,u,w,n] at h ⊢
  omega
theorem coupledPadded_exception_global (g : Cap)
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    coupledPadded g + paddedExceptionCap g < budget := by
  by_cases hs10 : g.inner ≤ 10
  · have h := casePadded_s10 hL hy hs10
    simp only [paddedExceptionCap,if_pos hs10]
    exact h.trans_lt (by norm_num [budget,prime])
  have hs11 : g.inner = 11 := by omega
  by_cases hy53 : g.middle ≤ 53
  · have h := casePadded_y53 hL hy53 hs11 hn1 hn2
    simp only [paddedExceptionCap,if_neg hs10,if_pos hy53,add_zero]
    exact h.trans_lt (by norm_num [budget,prime])
  have hy54 : g.middle = 54 := by omega
  by_cases hL1206 : g.total ≤ 1206
  · have h := casePadded_y54_low (by omega) hL1206 hy54 hs11
    simp only [paddedExceptionCap,if_neg hs10,if_neg hy53,if_pos hL1206]
    exact h.trans_lt (by norm_num [budget,prime])
  · have h := casePadded_y54_high (by omega) hL hy54 hs11
    simp only [paddedExceptionCap,if_neg hs10,if_neg hy53,if_neg hL1206]
    exact h.trans_lt (by norm_num [budget,prime])
theorem actualLedgerPadded_exception_lt_budget {qA qB qH qC g : Cap}
    (exception : Nat) (hexception : exception ≤ paddedExceptionCap g)
    (hA : CapLE qA (sub parentA g))
    (hB : CapLE qB (sub parentB g))
    (hH : CapLE qH (sub hmax g))
    (hC : CapLE qC (sub parentC g))
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    actualLedgerPadded qA qB qH qC g + exception < budget := by
  have hledger := actualLedgerPadded_le_coupled hA hB hH hC
  exact (Nat.add_le_add hledger hexception).trans_lt
    (coupledPadded_exception_global g hL hy hs hn1 hn2)
theorem actualLedgerPadded_lt_budget {qA qB qH qC g : Cap}
    (hA : CapLE qA (sub parentA g))
    (hB : CapLE qB (sub parentB g))
    (hH : CapLE qH (sub hmax g))
    (hC : CapLE qC (sub parentC g))
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    actualLedgerPadded qA qB qH qC g < budget := by
  simpa only [Nat.add_zero] using
    actualLedgerPadded_exception_lt_budget (g := g) 0 (Nat.zero_le _)
      hA hB hH hC hL hy hs hn1 hn2
theorem padded_coarse_slack :
    budget - 272979521442990893 = 2001205668404194 := by
  norm_num [budget,prime]
end ProximityPrize.SubmissionLower.ContactKernelArithmetic6733Research
