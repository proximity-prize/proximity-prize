import ProximityPrize.SubmissionLower.HigherRootSources6810
import Mathlib.Tactic.Ring

/- UNCOMPILED DRAFT. Arithmetic identities only; no geometry or protocol claim. -/
namespace DualCutBridge6807Arithmetic

structure Tri where
  z : ℕ
  v : ℕ
  r : ℕ

def mixed (p q t : Tri) : ℕ :=
  p.r*q.r*t.r + p.z*q.r*t.r + q.z*p.r*t.r + t.z*p.r*q.r +
  p.v*q.r*t.r + q.v*p.r*t.r + t.v*p.r*q.r +
  p.r*q.v*t.v + q.r*p.v*t.v + t.r*p.v*q.v +
  p.z*q.v*t.r + p.z*t.v*q.r + q.z*p.v*t.r +
  q.z*t.v*p.r + t.z*p.v*q.r + t.z*q.v*p.r

def firstFlag (d vz vv vr a b c : ℕ) : Tri :=
  ⟨d*(131070*c)+131071*vz, d*(131070*b+131069)+131071*vv,
   d*(131070*a+131070)+131071*vr⟩

def secondFlag (d vz vv vr a b c : ℕ) : Tri :=
  ⟨d*(131074*c)+65539*vz, d*(131074*b+131076)+65539*vv,
   d*(131074*a+262148)+65539*vr⟩

def graphNumerator (p : Tri) (d vz vv vr a b c : ℕ) : ℕ :=
  mixed p (firstFlag d vz vv vr a b c) (secondFlag d vz vv vr a b c)

def identityDegree (p : Tri) (a b c : ℕ) : ℕ :=
  p.z*(655365+262146*a) + p.v*(1310730+524292*a) +
  p.r*(2097170+524292*a+524292*b+262146*c)

def earlySlackZ (a b c : ℕ) : ℕ :=
  7772894215673728329 + 442898737757451360*b + 1314197199780763824*a + 62160477544982880*a*b + 31080238772491440*a^2

def earlySlackV (a b c : ℕ) : ℕ :=
  123714932797994053311 + 442898737757451360*c + 442898737757451360*b + 18642733915621903992*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

def earlySlackR (a b c : ℕ) : ℕ :=
  374269022993650786110 + 1314197199780763824*c + 18642733915621903992*b + 62160477544982880*b*c + 31080238772491440*b^2 + 18642733915621903992*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

theorem early_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 6 2243 117 45 a b c =
      36 * 131073 * 80821 * identityDegree p a b c +
      (p.z*earlySlackZ a b c + p.v*earlySlackV a b c + p.r*earlySlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    earlySlackZ, earlySlackV, earlySlackR]
  ring

theorem early_absorption (p : Tri) (a b c : ℕ) :
    36 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 6 2243 117 45 a b c := by
  rw [early_identity]
  exact Nat.le_add_right _ _

def mainSlackZ (a b c : ℕ) : ℕ :=
  9843685559207202240 + 497289985537003344*b + 1492911299627863200*a + 62160477544982880*a*b + 31080238772491440*a^2

def mainSlackV (a b c : ℕ) : ℕ :=
  143795656961257574460 + 497289985537003344*c + 497289985537003344*b + 19419751741044075192*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

def mainSlackR (a b c : ℕ) : ℕ :=
  436625653532774777103 + 1492911299627863200*c + 19419751741044075192*b + 62160477544982880*b*c + 31080238772491440*b^2 + 19419751741044075192*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

theorem main_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 6 2320 133 52 a b c =
      36 * 131073 * 80821 * identityDegree p a b c +
      (p.z*mainSlackZ a b c + p.v*mainSlackV a b c + p.r*mainSlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    mainSlackZ, mainSlackV, mainSlackR]
  ring

theorem main_absorption (p : Tri) (a b c : ℕ) :
    36 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 6 2320 133 52 a b c := by
  rw [main_identity]
  exact Nat.le_add_right _ _

def wideSlackZ (a b c : ℕ) : ℕ :=
  9350241268618662639 + 401458221792298020*b + 1229919223006250340*a + 43166998295127000*a*b + 21583499147563500*a^2

def wideSlackV (a b c : ℕ) : ℕ :=
  121664966463379579974 + 401458221792298020*c + 401458221792298020*b + 14240293514572410090*a + 43166998295127000*a*c + 43166998295127000*a*b + 21583499147563500*a^2

def wideSlackR (a b c : ℕ) : ℕ :=
  373144352918145834762 + 1229919223006250340*c + 14240293514572410090*b + 43166998295127000*b*c + 21583499147563500*b^2 + 14240293514572410090*a + 43166998295127000*a*c + 43166998295127000*a*b + 21583499147563500*a^2

theorem wide_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 5 2020 132 52 a b c =
      25 * 131073 * 80821 * identityDegree p a b c +
      (p.z*wideSlackZ a b c + p.v*wideSlackV a b c + p.r*wideSlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    wideSlackZ, wideSlackV, wideSlackR]
  ring

theorem wide_absorption (p : Tri) (a b c : ℕ) :
    25 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 5 2020 132 52 a b c := by
  rw [wide_identity]
  exact Nat.le_add_right _ _

def band_d1SlackZ (a b c : ℕ) : ℕ :=
  7367114088668631135 + 69931564767629124*b + 234645023254341540*a + 1726679931805080*a*b + 863339965902540*a^2

def band_d1SlackV (a b c : ℕ) : ℕ :=
  27122753669095645230 + 69931564767629124*c + 69931564767629124*b + 775780470261579162*a + 1726679931805080*a*c + 1726679931805080*a*b + 863339965902540*a^2

def band_d1SlackR (a b c : ℕ) : ℕ :=
  81312645473350312998 + 234645023254341540*c + 775780470261579162*b + 1726679931805080*b*c + 863339965902540*b^2 + 775780470261579162*a + 1726679931805080*a*c + 1726679931805080*a*b + 863339965902540*a^2

theorem band_d1_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 1 420 128 52 a b c =
      1 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d1SlackZ a b c + p.v*band_d1SlackV a b c + p.r*band_d1SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d1SlackZ, band_d1SlackV, band_d1SlackR]
  ring

theorem band_d1_absorption (p : Tri) (a b c : ℕ) :
    1 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 1 420 128 52 a b c := by
  rw [band_d1_identity]
  exact Nat.le_add_right _ _

def band_d2SlackZ (a b c : ℕ) : ℕ :=
  7864298386295519976 + 145043169330673488*b + 474959457182137344*a + 6906719727220320*a*b + 3453359863610160*a^2

def band_d2SlackV (a b c : ℕ) : ℕ :=
  33426842596089362916 + 145043169330673488*c + 145043169330673488*b + 1810682231427438552*a + 6906719727220320*a*c + 6906719727220320*a*b + 3453359863610160*a^2

def band_d2SlackR (a b c : ℕ) : ℕ :=
  100176681231420924699 + 474959457182137344*c + 1810682231427438552*b + 6906719727220320*b*c + 3453359863610160*b^2 + 1810682231427438552*a + 6906719727220320*a*c + 6906719727220320*a*b + 3453359863610160*a^2

theorem band_d2_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 2 520 129 52 a b c =
      4 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d2SlackZ a b c + p.v*band_d2SlackV a b c + p.r*band_d2SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d2SlackZ, band_d2SlackV, band_d2SlackR]
  ring

theorem band_d2_absorption (p : Tri) (a b c : ℕ) :
    4 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 2 520 129 52 a b c := by
  rw [band_d2_identity]
  exact Nat.le_add_right _ _

def band_d3SlackZ (a b c : ℕ) : ℕ :=
  8360547682162821507 + 225334813689133092*b + 720943301783387412*a + 15540119386245720*a*b + 7770059693122860*a^2

def band_d3SlackV (a b c : ℕ) : ℕ :=
  40147786619742325002 + 225334813689133092*c + 225334813689133092*b + 3104705283497578170*a + 15540119386245720*a*c + 15540119386245720*a*b + 7770059693122860*a^2

def band_d3SlackR (a b c : ℕ) : ℕ :=
  119877772501936395360 + 720943301783387412*c + 3104705283497578170*b + 15540119386245720*b*c + 7770059693122860*b^2 + 3104705283497578170*a + 15540119386245720*a*c + 15540119386245720*a*b + 7770059693122860*a^2

theorem band_d3_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 3 620 130 52 a b c =
      9 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d3SlackZ a b c + p.v*band_d3SlackV a b c + p.r*band_d3SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d3SlackZ, band_d3SlackV, band_d3SlackR]
  ring

theorem band_d3_absorption (p : Tri) (a b c : ℕ) :
    9 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 3 620 130 52 a b c := by
  rw [band_d3_identity]
  exact Nat.le_add_right _ _

def band_d4SlackZ (a b c : ℕ) : ℕ :=
  8855861976270535728 + 310806497843007936*b + 972596557058091744*a + 27626878908881280*a*b + 13813439454440640*a^2

def band_d4SlackV (a b c : ℕ) : ℕ :=
  52638475322737209888 + 310806497843007936*c + 310806497843007936*b + 5175861510086778816*a + 27626878908881280*a*c + 27626878908881280*a*b + 13813439454440640*a^2

def band_d4SlackR (a b c : ℕ) : ℕ :=
  157597009688016701181 + 972596557058091744*c + 5175861510086778816*b + 27626878908881280*b*c + 13813439454440640*b^2 + 5175861510086778816*a + 27626878908881280*a*c + 27626878908881280*a*b + 13813439454440640*a^2

theorem band_d4_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 4 820 131 52 a b c =
      16 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d4SlackZ a b c + p.v*band_d4SlackV a b c + p.r*band_d4SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d4SlackZ, band_d4SlackV, band_d4SlackR]
  ring

theorem band_d4_absorption (p : Tri) (a b c : ℕ) :
    16 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 4 820 131 52 a b c := by
  rw [band_d4_identity]
  exact Nat.le_add_right _ _

def band_d5SlackZ (a b c : ℕ) : ℕ :=
  9350241268618662639 + 401458221792298020*b + 1229919223006250340*a + 43166998295127000*a*b + 21583499147563500*a^2

def band_d5SlackV (a b c : ℕ) : ℕ :=
  71546421583614381774 + 401458221792298020*c + 401458221792298020*b + 8412659823906126090*a + 43166998295127000*a*c + 43166998295127000*a*b + 21583499147563500*a^2

def band_d5SlackR (a b c : ℕ) : ℕ :=
  214629429414762893862 + 1229919223006250340*c + 8412659823906126090*b + 43166998295127000*b*c + 21583499147563500*b^2 + 8412659823906126090*a + 43166998295127000*a*c + 43166998295127000*a*b + 21583499147563500*a^2

theorem band_d5_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 5 1120 132 52 a b c =
      25 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d5SlackZ a b c + p.v*band_d5SlackV a b c + p.r*band_d5SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d5SlackZ, band_d5SlackV, band_d5SlackR]
  ring

theorem band_d5_absorption (p : Tri) (a b c : ℕ) :
    25 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 5 1120 132 52 a b c := by
  rw [band_d5_identity]
  exact Nat.le_add_right _ _

def band_d6SlackZ (a b c : ℕ) : ℕ :=
  9843685559207202240 + 497289985537003344*b + 1492911299627863200*a + 62160477544982880*a*b + 31080238772491440*a^2

def band_d6SlackV (a b c : ℕ) : ℕ :=
  103303703115957126060 + 497289985537003344*c + 497289985537003344*b + 13980626963088876792*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

def band_d6SlackR (a b c : ℕ) : ℕ :=
  310314516460463369103 + 1492911299627863200*c + 13980626963088876792*b + 62160477544982880*b*c + 31080238772491440*b^2 + 13980626963088876792*a + 62160477544982880*a*c + 62160477544982880*a*b + 31080238772491440*a^2

theorem band_d6_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 6 1620 133 52 a b c =
      36 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d6SlackZ a b c + p.v*band_d6SlackV a b c + p.r*band_d6SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d6SlackZ, band_d6SlackV, band_d6SlackR]
  ring

theorem band_d6_absorption (p : Tri) (a b c : ℕ) :
    36 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 6 1620 133 52 a b c := by
  rw [band_d6_identity]
  exact Nat.le_add_right _ _

def band_d7SlackZ (a b c : ℕ) : ℕ :=
  10336194848036154531 + 598301789077123908*b + 1761572786922930324*a + 84607316658448920*a*b + 42303658329224460*a^2

def band_d7SlackV (a b c : ℕ) : ℕ :=
  161206150599292256346 + 598301789077123908*c + 598301789077123908*b + 24469822345708934922*a + 84607316658448920*a*c + 84607316658448920*a*b + 42303658329224460*a^2

def band_d7SlackR (a b c : ℕ) : ℕ :=
  484194598131762286104 + 1761572786922930324*c + 24469822345708934922*b + 84607316658448920*b*c + 42303658329224460*b^2 + 24469822345708934922*a + 84607316658448920*a*c + 84607316658448920*a*b + 42303658329224460*a^2

theorem band_d7_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 7 2520 134 52 a b c =
      49 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d7SlackZ a b c + p.v*band_d7SlackV a b c + p.r*band_d7SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d7SlackZ, band_d7SlackV, band_d7SlackR]
  ring

theorem band_d7_absorption (p : Tri) (a b c : ℕ) :
    49 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 7 2520 134 52 a b c := by
  rw [band_d7_identity]
  exact Nat.le_add_right _ _

def band_d8SlackZ (a b c : ℕ) : ℕ :=
  10827769135105519512 + 704493632412659712*b + 2035903684891451712*a + 110507515635525120*a*b + 55253757817762560*a^2

def band_d8SlackV (a b c : ℕ) : ℕ :=
  353519897033635017432 + 704493632412659712*c + 704493632412659712*b + 59046685665513190080*a + 110507515635525120*a*c + 110507515635525120*a*b + 55253757817762560*a^2

def band_d8SlackR (a b c : ℕ) : ℕ :=
  1062882521284393952265 + 2035903684891451712*c + 59046685665513190080*b + 110507515635525120*b*c + 55253757817762560*b^2 + 59046685665513190080*a + 110507515635525120*a*c + 110507515635525120*a*b + 55253757817762560*a^2

theorem band_d8_identity (p : Tri) (a b c : ℕ) :
    50253 * graphNumerator p 8 5520 135 52 a b c =
      64 * 131073 * 80821 * identityDegree p a b c +
      (p.z*band_d8SlackZ a b c + p.v*band_d8SlackV a b c + p.r*band_d8SlackR a b c) := by
  simp [graphNumerator, mixed, firstFlag, secondFlag, identityDegree,
    band_d8SlackZ, band_d8SlackV, band_d8SlackR]
  ring

theorem band_d8_absorption (p : Tri) (a b c : ℕ) :
    64 * 131073 * 80821 * identityDegree p a b c ≤
      50253 * graphNumerator p 8 5520 135 52 a b c := by
  rw [band_d8_identity]
  exact Nat.le_add_right _ _

theorem powered_cut_divisor_identity (d w lc tail j m v : ℤ) :
    w*lc + d*tail + d*j + w*v =
      d*(tail+j+w*m) + w*(v-d*m+lc) := by
  ring

end DualCutBridge6807Arithmetic
