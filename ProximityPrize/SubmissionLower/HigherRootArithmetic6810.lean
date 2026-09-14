import ProximityPrize.SubmissionLower.HigherRootSources6810
import ProximityPrize.SubmissionLower.DualCutBridge6807Arithmetic

namespace ProximityPrize.SubmissionLower.HigherRootArithmetic6810
open DualCutBridge6807Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- The numerical coefficient/helper numerator at agreement 181294.
This definition alone makes no claim about a geometric counting theorem. -/
def pairNumerator (a b c capY capR capT : ℕ) : ℕ :=
  131073*((1+262142*(a+b+5))*((a+3)*capT+(a+b+c+5)*capR) +
    131071*(2*a+5)*((a+b+5)*capT+(a+b+c+5)*capY) +
    (1+262142*(a+b+c+5))*((a+b+5)*capR+(a+3)*capY)) +
    80851*50223*((a+b+5)*capR+(a+3)*capY)

namespace P0
def ownPolynomial (a b c : ℕ) : ℕ :=
    31061684513777040*a^3 +
    93185053541331120*a^2*b +
    93185053541331120*a^2*c +
    14332448008943080776*a^2 +
    93185053541331120*a*b^2 +
    186370107082662240*a*b*c +
    28659997693584704592*a*b +
    3495062716032425904*a*c +
    381828443789848714509*a +
    590311757921188032*b^2 +
    1180489925179609056*b*c +
    147266723512066384188*b +
    15859271878212815964*c +
    1140339730208110118919

def helperSlack (a b c : ℕ) : ℕ :=
    30883563630087696*a^3 +
    92828811773952432*a^2*b +
    93006932657641776*a^2*c +
    14320269398089472904*a^2 +
    93006932657641776*a*b^2 +
    186191986198972896*a*b*c +
    28647106599196339344*a*b +
    3492628397062177392*a*c +
    381741744644671860957*a +
    589599274386430656*b^2 +
    1179777441644851680*b*c +
    147232951116623756460*b +
    15853423574789168652*c +
    1140188532913569293847

def identitySlackZ (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    1491923271549502080*a +
    496993113717089904*b +
    9837567105446057040

def identitySlackV (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    62123369027554080*a*c +
    13972087236486310632*a +
    496993113717089904*b +
    496993113717089904*c +
    103241548990359769860

def identitySlackR (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    62123369027554080*a*c +
    13972087236486310632*a +
    31061684513777040*b^2 +
    62123369027554080*b*c +
    13972087236486310632*b +
    1491923271549502080*c +
    310128490793952163173

def fullSlope (a b : ℕ) : ℕ :=
    93185172034062156*a^2 +
    186370344068124312*a*b +
    3495064960849756458*a +
    1180490899463621736*b +
    15859278072885481230

def fullIntercept (a b : ℕ) : ℕ :=
    31061724011354052*a^3 +
    93185172034062156*a^2*b +
    14332454463687365193*a^2 +
    93185172034062156*a*b^2 +
    28660010603073273426*a*b +
    381828505374973282779*a +
    590312245063194372*b^2 +
    147266761700752764294*b +
    1140339858463875096228

def coefficientNumerator (a b c : ℕ) : ℕ := pairNumerator a b c 180 54 1800
def helperNumerator (a b c : ℕ) : ℕ :=
  pairNumerator a b c (180+24*(a+b+4)) (54+24*(a+2)) (1800+24*(a+b+c+4))

theorem own_identity (a b c : ℕ) : ownPolynomial a b c =
    50223*graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
      36*coefficientNumerator a b c := by
  simp only [ownPolynomial, coefficientNumerator, pairNumerator,
    graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_identity (a b c : ℕ) : ownPolynomial a b c =
    36*helperNumerator a b c + helperSlack a b c + 36*coefficientNumerator a b c := by
  simp only [ownPolynomial, helperNumerator, helperSlack, coefficientNumerator, pairNumerator]
  ring

theorem identity_absorption (p : Tri) (a b c : ℕ) :
    36*131073*80851*identityDegree p a b c ≤
      50223*graphNumerator p 6 1620 133 52 a b c := by
  have h : 50223*graphNumerator p 6 1620 133 52 a b c =
      36*131073*80851*identityDegree p a b c +
      (p.z*identitySlackZ a b c+p.v*identitySlackV a b c+p.r*identitySlackR a b c) := by
    simp only [graphNumerator, identityDegree, mixed, firstFlag, secondFlag,
      identitySlackZ, identitySlackV, identitySlackR]
    ring
  rw [h]
  exact Nat.le_add_right _ _

theorem rounded_sum_le (x y : ℕ) :
    x/36+y/50223 ≤ (50223*x+36*y)/1808028 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c/36 +
      coefficientNumerator a b c/50223 ≤ ownPolynomial a b c/1808028 := by
  rw [own_identity]
  exact rounded_sum_le _ _

theorem helper_cap_le (a b c : ℕ) :
    helperNumerator a b c/50223 ≤ ownPolynomial a b c/1808028 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_identity]
  nlinarith

/-- Full surface conductor is charged once for this chosen source profile.
No independent choice of profiles for separate geometric components is used. -/
def fullNumerator (a b c : ℕ) : ℕ :=
  ownPolynomial a b c + 50223*mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩
    (secondFlag 6 1620 133 52 a b c)

theorem full_numerator_identity (a b c : ℕ) : fullNumerator a b c =
    50223*(graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
      mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩ (secondFlag 6 1620 133 52 a b c)) +
      36*coefficientNumerator a b c := by
  rw [fullNumerator, own_identity]
  ring

theorem full_affine_identity (a b c : ℕ) :
    fullNumerator a b c = fullSlope a b*c+fullIntercept a b := by
  simp only [fullNumerator, ownPolynomial, mixed, secondFlag, fullSlope, fullIntercept]
  ring

def roundedCap (a b c : ℕ) : ℕ :=
  (fullSlope a b/1808028+1)*c+(fullIntercept a b/1808028+1)

theorem full_cap_le_rounded (a b c : ℕ) :
    fullNumerator a b c/1808028 ≤ roundedCap a b c := by
  rw [full_affine_identity]
  unfold roundedCap
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 1808028)).mpr
  have hs := Nat.lt_mul_div_succ (fullSlope a b) (by decide : 0 < 1808028)
  have hi := Nat.lt_mul_div_succ (fullIntercept a b) (by decide : 0 < 1808028)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  nlinarith

#print axioms identity_absorption
#print axioms retained_cap_le
#print axioms helper_cap_le
#print axioms full_numerator_identity
#print axioms full_cap_le_rounded
end P0

namespace P1
def ownPolynomial (a b c : ℕ) : ℕ :=
    42278403921529860*a^3 +
    126835211764589580*a^2*b +
    126835211764589580*a^2*c +
    25392574207335888882*a^2 +
    126835211764589580*a*b^2 +
    253670423529179160*a*b*c +
    50775285726651724392*a*b +
    4216607590091075340*a*c +
    619975411972020975867*a +
    743087985755501064*b^2 +
    1485987405266849520*b*c +
    246183864197644402587*b +
    17841928718877469176*c +
    1821083303401215375849

def helperSlack (a b c : ℕ) : ℕ :=
    42025859844539760*a^3 +
    126330123610609380*a^2*b +
    126582667687599480*a^2*c +
    25369473311500392522*a^2 +
    126582667687599480*a*b^2 +
    253417879452189060*a*b*c +
    50751176338135447566*a*b +
    4213208346493659744*a*c +
    619807282994452026183*a +
    742079493074720598*b^2 +
    1484978912586069054*b*c +
    246119950325643580884*b +
    17833784170872387702*c +
    1820788746283072875951

def identitySlackZ (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    1760389421211488004*a +
    616064207746758876*b +
    10577334817095277719

def identitySlackV (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    84556807843059720*a*c +
    24898880897040161718*a +
    616064207746758876*b +
    616064207746758876*c +
    168728698693252205730

def identitySlackR (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    84556807843059720*a*c +
    24898880897040161718*a +
    42278403921529860*b^2 +
    84556807843059720*b*c +
    24898880897040161718*b +
    1760389421211488004*c +
    492952387649789282925

def fullSlope (a b : ℕ) : ℕ :=
    126835350006109122*a^2 +
    253670700012218244*a*b +
    4216610012647904232*a +
    1485988498043995020*b +
    17841935269030336470

def fullIntercept (a b : ℕ) : ℕ :=
    42278450002036374*a^3 +
    126835350006109122*a^2*b +
    25392583874645294421*a^2 +
    126835350006109122*a*b^2 +
    50775305061270535470*a*b +
    619975505189077042707*a +
    743088532144073814*b^2 +
    246183921483983216439*b +
    1821083497817428658892

def coefficientNumerator (a b c : ℕ) : ℕ := pairNumerator a b c 180 56 2749
def helperNumerator (a b c : ℕ) : ℕ :=
  pairNumerator a b c (180+25*(a+b+4)) (56+25*(a+2)) (2749+25*(a+b+c+4))

theorem own_identity (a b c : ℕ) : ownPolynomial a b c =
    50223*graphNumerator ⟨c,b+2,a+3⟩ 7 2569 132 54 a b c +
      49*coefficientNumerator a b c := by
  simp only [ownPolynomial, coefficientNumerator, pairNumerator,
    graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_identity (a b c : ℕ) : ownPolynomial a b c =
    49*helperNumerator a b c + helperSlack a b c + 49*coefficientNumerator a b c := by
  simp only [ownPolynomial, helperNumerator, helperSlack, coefficientNumerator, pairNumerator]
  ring

theorem identity_absorption (p : Tri) (a b c : ℕ) :
    49*131073*80851*identityDegree p a b c ≤
      50223*graphNumerator p 7 2569 132 54 a b c := by
  have h : 50223*graphNumerator p 7 2569 132 54 a b c =
      49*131073*80851*identityDegree p a b c +
      (p.z*identitySlackZ a b c+p.v*identitySlackV a b c+p.r*identitySlackR a b c) := by
    simp only [graphNumerator, identityDegree, mixed, firstFlag, secondFlag,
      identitySlackZ, identitySlackV, identitySlackR]
    ring
  rw [h]
  exact Nat.le_add_right _ _

theorem rounded_sum_le (x y : ℕ) :
    x/49+y/50223 ≤ (50223*x+49*y)/2460927 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have hx := Nat.div_mul_le_self x 49
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 7 2569 132 54 a b c/49 +
      coefficientNumerator a b c/50223 ≤ ownPolynomial a b c/2460927 := by
  rw [own_identity]
  exact rounded_sum_le _ _

theorem helper_cap_le (a b c : ℕ) :
    helperNumerator a b c/50223 ≤ ownPolynomial a b c/2460927 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_identity]
  nlinarith

/-- Full surface conductor is charged once for this chosen source profile.
No independent choice of profiles for separate geometric components is used. -/
def fullNumerator (a b c : ℕ) : ℕ :=
  ownPolynomial a b c + 50223*mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩
    (secondFlag 7 2569 132 54 a b c)

theorem full_numerator_identity (a b c : ℕ) : fullNumerator a b c =
    50223*(graphNumerator ⟨c,b+2,a+3⟩ 7 2569 132 54 a b c +
      mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩ (secondFlag 7 2569 132 54 a b c)) +
      49*coefficientNumerator a b c := by
  rw [fullNumerator, own_identity]
  ring

theorem full_affine_identity (a b c : ℕ) :
    fullNumerator a b c = fullSlope a b*c+fullIntercept a b := by
  simp only [fullNumerator, ownPolynomial, mixed, secondFlag, fullSlope, fullIntercept]
  ring

def roundedCap (a b c : ℕ) : ℕ :=
  (fullSlope a b/2460927+1)*c+(fullIntercept a b/2460927+1)

theorem full_cap_le_rounded (a b c : ℕ) :
    fullNumerator a b c/2460927 ≤ roundedCap a b c := by
  rw [full_affine_identity]
  unfold roundedCap
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2460927)).mpr
  have hs := Nat.lt_mul_div_succ (fullSlope a b) (by decide : 0 < 2460927)
  have hi := Nat.lt_mul_div_succ (fullIntercept a b) (by decide : 0 < 2460927)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  nlinarith

#print axioms identity_absorption
#print axioms retained_cap_le
#print axioms helper_cap_le
#print axioms full_numerator_identity
#print axioms full_cap_le_rounded
end P1

namespace P2
def ownPolynomial (a b c : ℕ) : ℕ :=
    42278403921529860*a^3 +
    126835211764589580*a^2*b +
    126835211764589580*a^2*c +
    23371505588403516306*a^2 +
    126835211764589580*a*b^2 +
    253670423529179160*a*b*c +
    46733882550237430464*a*b +
    4307222388581794920*a*c +
    578801417095321207518*a +
    743087985755501064*b^2 +
    1485987405266849520*b*c +
    226363098048488547243*b +
    18286341554054673291*c +
    1700357823101681476866

def helperSlack (a b c : ℕ) : ℕ :=
    42025859844539760*a^3 +
    126330123610609380*a^2*b +
    126582667687599480*a^2*c +
    23349872815468922394*a^2 +
    126582667687599480*a*b^2 +
    253417879452189060*a*b*c +
    46711241284622056086*a*b +
    4303789472440780644*a*c +
    578644664083350406608*a +
    742079493074720598*b^2 +
    1484978912586069054*b*c +
    226303221514465207272*b +
    18278104406554695447*c +
    1700083446712774850034

def identitySlackZ (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    1805688402320948124*a +
    616064207746758876*b +
    10885804409196653289

def identitySlackV (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    84556807843059720*a*c +
    22878546339558240366*a +
    616064207746758876*b +
    616064207746758876*c +
    154970954885530855308

def identitySlackR (a b c : ℕ) : ℕ :=
    42278403921529860*a^2 +
    84556807843059720*a*b +
    84556807843059720*a*c +
    22878546339558240366*a +
    42278403921529860*b^2 +
    84556807843059720*b*c +
    22878546339558240366*b +
    1805688402320948124*c +
    461885753543298195723

def fullSlope (a b : ℕ) : ℕ :=
    126835350006109122*a^2 +
    253670700012218244*a*b +
    4307224844054275782*a +
    1485988498043995020*b +
    18286348202954496495

def fullIntercept (a b : ℕ) : ℕ :=
    42278450002036374*a^3 +
    126835350006109122*a^2*b +
    23371514521693882914*a^2 +
    126835350006109122*a*b^2 +
    46733900416818163680*a*b +
    578801502972186885048*a +
    743088532144073814*b^2 +
    226363150930713127509*b +
    1700358002103494942358

def coefficientNumerator (a b c : ℕ) : ℕ := pairNumerator a b c 185 56 2526
def helperNumerator (a b c : ℕ) : ℕ :=
  pairNumerator a b c (185+25*(a+b+4)) (56+25*(a+2)) (2526+25*(a+b+c+4))

theorem own_identity (a b c : ℕ) : ownPolynomial a b c =
    50223*graphNumerator ⟨c,b+2,a+3⟩ 7 2341 137 54 a b c +
      49*coefficientNumerator a b c := by
  simp only [ownPolynomial, coefficientNumerator, pairNumerator,
    graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_identity (a b c : ℕ) : ownPolynomial a b c =
    49*helperNumerator a b c + helperSlack a b c + 49*coefficientNumerator a b c := by
  simp only [ownPolynomial, helperNumerator, helperSlack, coefficientNumerator, pairNumerator]
  ring

theorem identity_absorption (p : Tri) (a b c : ℕ) :
    49*131073*80851*identityDegree p a b c ≤
      50223*graphNumerator p 7 2341 137 54 a b c := by
  have h : 50223*graphNumerator p 7 2341 137 54 a b c =
      49*131073*80851*identityDegree p a b c +
      (p.z*identitySlackZ a b c+p.v*identitySlackV a b c+p.r*identitySlackR a b c) := by
    simp only [graphNumerator, identityDegree, mixed, firstFlag, secondFlag,
      identitySlackZ, identitySlackV, identitySlackR]
    ring
  rw [h]
  exact Nat.le_add_right _ _

theorem rounded_sum_le (x y : ℕ) :
    x/49+y/50223 ≤ (50223*x+49*y)/2460927 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have hx := Nat.div_mul_le_self x 49
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 7 2341 137 54 a b c/49 +
      coefficientNumerator a b c/50223 ≤ ownPolynomial a b c/2460927 := by
  rw [own_identity]
  exact rounded_sum_le _ _

theorem helper_cap_le (a b c : ℕ) :
    helperNumerator a b c/50223 ≤ ownPolynomial a b c/2460927 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_identity]
  nlinarith

/-- Full surface conductor is charged once for this chosen source profile.
No independent choice of profiles for separate geometric components is used. -/
def fullNumerator (a b c : ℕ) : ℕ :=
  ownPolynomial a b c + 50223*mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩
    (secondFlag 7 2341 137 54 a b c)

theorem full_numerator_identity (a b c : ℕ) : fullNumerator a b c =
    50223*(graphNumerator ⟨c,b+2,a+3⟩ 7 2341 137 54 a b c +
      mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩ (secondFlag 7 2341 137 54 a b c)) +
      49*coefficientNumerator a b c := by
  rw [fullNumerator, own_identity]
  ring

theorem full_affine_identity (a b c : ℕ) :
    fullNumerator a b c = fullSlope a b*c+fullIntercept a b := by
  simp only [fullNumerator, ownPolynomial, mixed, secondFlag, fullSlope, fullIntercept]
  ring

def roundedCap (a b c : ℕ) : ℕ :=
  (fullSlope a b/2460927+1)*c+(fullIntercept a b/2460927+1)

theorem full_cap_le_rounded (a b c : ℕ) :
    fullNumerator a b c/2460927 ≤ roundedCap a b c := by
  rw [full_affine_identity]
  unfold roundedCap
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2460927)).mpr
  have hs := Nat.lt_mul_div_succ (fullSlope a b) (by decide : 0 < 2460927)
  have hi := Nat.lt_mul_div_succ (fullIntercept a b) (by decide : 0 < 2460927)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  nlinarith

#print axioms identity_absorption
#print axioms retained_cap_le
#print axioms helper_cap_le
#print axioms full_numerator_identity
#print axioms full_cap_le_rounded
end P2

namespace P3
def ownPolynomial (a b c : ℕ) : ℕ :=
    31061684513777040*a^3 +
    93185053541331120*a^2*b +
    93185053541331120*a^2*c +
    21284745892242825096*a^2 +
    93185053541331120*a*b^2 +
    186370107082662240*a*b*c +
    42562433744469459936*a*b +
    3153304755771913296*a*c +
    530046453116734269621*a +
    528167649761772480*b^2 +
    1056221500070076768*b*c +
    201371128270918727676*b +
    13094450780979346668*c +
    1547465846884102902495

def helperSlack (a b c : ℕ) : ℕ :=
    30905828740548864*a^3 +
    92873341994874768*a^2*b +
    93029197768102944*a^2*c +
    21268551779993993256*a^2 +
    93029197768102944*a*b^2 +
    186214251309434064*a*b*c +
    42545622393880621272*a*b +
    3151178437524689376*a*c +
    529927687324041598149*a +
    527550411421765656*b^2 +
    1055604261730069944*b*c +
    201326393603522975136*b +
    13089357636031784772*c +
    1547257475055373815639

def identitySlackZ (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    1321081399936681056*a +
    434868796766973168*b +
    7709768884055849688

def identitySlackV (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    62123369027554080*a*c +
    20922245195280620472*a +
    434868796766973168*b +
    434868796766973168*c +
    136613988370129361568

def identitySlackR (a b c : ℕ) : ℕ :=
    31061684513777040*a^2 +
    62123369027554080*a*b +
    62123369027554080*a*c +
    20922245195280620472*a +
    31061684513777040*b^2 +
    62123369027554080*b*c +
    20922245195280620472*b +
    1321081399936681056*c +
    423579174823552264845

def fullSlope (a b : ℕ) : ℕ :=
    93185172034062156*a^2 +
    186370344068124312*a*b +
    3153306855760375182*a +
    1056222421689046296*b +
    13094456435835319626

def fullIntercept (a b : ℕ) : ℕ :=
    31061724011354052*a^3 +
    93185172034062156*a^2*b +
    21284755292937960828*a^2 +
    93185172034062156*a*b^2 +
    42562452545859731400*a*b +
    530046544161367351041*a +
    528168110571257244*b^2 +
    201371184029980129368*b +
    1547466036899505671115

def coefficientNumerator (a b c : ℕ) : ℕ := pairNumerator a b c 158 46 2695
def helperNumerator (a b c : ℕ) : ℕ :=
  pairNumerator a b c (158+21*(a+b+4)) (46+21*(a+2)) (2695+21*(a+b+c+4))

theorem own_identity (a b c : ℕ) : ownPolynomial a b c =
    50223*graphNumerator ⟨c,b+2,a+3⟩ 6 2537 119 44 a b c +
      36*coefficientNumerator a b c := by
  simp only [ownPolynomial, coefficientNumerator, pairNumerator,
    graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_identity (a b c : ℕ) : ownPolynomial a b c =
    36*helperNumerator a b c + helperSlack a b c + 36*coefficientNumerator a b c := by
  simp only [ownPolynomial, helperNumerator, helperSlack, coefficientNumerator, pairNumerator]
  ring

theorem identity_absorption (p : Tri) (a b c : ℕ) :
    36*131073*80851*identityDegree p a b c ≤
      50223*graphNumerator p 6 2537 119 44 a b c := by
  have h : 50223*graphNumerator p 6 2537 119 44 a b c =
      36*131073*80851*identityDegree p a b c +
      (p.z*identitySlackZ a b c+p.v*identitySlackV a b c+p.r*identitySlackR a b c) := by
    simp only [graphNumerator, identityDegree, mixed, firstFlag, secondFlag,
      identitySlackZ, identitySlackV, identitySlackR]
    ring
  rw [h]
  exact Nat.le_add_right _ _

theorem rounded_sum_le (x y : ℕ) :
    x/36+y/50223 ≤ (50223*x+36*y)/1808028 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 2537 119 44 a b c/36 +
      coefficientNumerator a b c/50223 ≤ ownPolynomial a b c/1808028 := by
  rw [own_identity]
  exact rounded_sum_le _ _

theorem helper_cap_le (a b c : ℕ) :
    helperNumerator a b c/50223 ≤ ownPolynomial a b c/1808028 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_identity]
  nlinarith

/-- Full surface conductor is charged once for this chosen source profile.
No independent choice of profiles for separate geometric components is used. -/
def fullNumerator (a b c : ℕ) : ℕ :=
  ownPolynomial a b c + 50223*mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩
    (secondFlag 6 2537 119 44 a b c)

theorem full_numerator_identity (a b c : ℕ) : fullNumerator a b c =
    50223*(graphNumerator ⟨c,b+2,a+3⟩ 6 2537 119 44 a b c +
      mixed ⟨c,b+2,a+3⟩ ⟨c,b+2,a+3⟩ (secondFlag 6 2537 119 44 a b c)) +
      36*coefficientNumerator a b c := by
  rw [fullNumerator, own_identity]
  ring

theorem full_affine_identity (a b c : ℕ) :
    fullNumerator a b c = fullSlope a b*c+fullIntercept a b := by
  simp only [fullNumerator, ownPolynomial, mixed, secondFlag, fullSlope, fullIntercept]
  ring

def roundedCap (a b c : ℕ) : ℕ :=
  (fullSlope a b/1808028+1)*c+(fullIntercept a b/1808028+1)

theorem full_cap_le_rounded (a b c : ℕ) :
    fullNumerator a b c/1808028 ≤ roundedCap a b c := by
  rw [full_affine_identity]
  unfold roundedCap
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 1808028)).mpr
  have hs := Nat.lt_mul_div_succ (fullSlope a b) (by decide : 0 < 1808028)
  have hi := Nat.lt_mul_div_succ (fullIntercept a b) (by decide : 0 < 1808028)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  nlinarith

#print axioms identity_absorption
#print axioms retained_cap_le
#print axioms helper_cap_le
#print axioms full_numerator_identity
#print axioms full_cap_le_rounded
end P3

end ProximityPrize.SubmissionLower.HigherRootArithmetic6810
