import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ


namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174
open RCN159 RCN086
open RCN095 RCN275
open RCN198 RCN263
open RCN146 RCN087
open RCN203 RCN084
open RCN313 RCN074
open RCN335

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80191
def agreements:ℕ:=181953
def gap:ℕ:=50882
def prime:ℕ:=2130706433
def weightedCap:ℕ:=8187885

abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600

def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w+1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w+2)

theorem row_values:
    agreements+errors=n ∧ agreements - w=gap ∧
    weightedCap=45*agreements ∧ w<agreements ∧
    w+1≤weightedCap ∧ weightedCap<prime:=by
  norm_num [agreements,errors,n,w,gap,weightedCap,prime]

theorem tail_support_formula (a b s d:ℕ):
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2*a*d,1+2*(b+1)*d,2*(s+1)*d⟩:=by
  have ht:a+b+s+3 - (b+s+3)=a:=by omega
  have hy:b+s+3 - (s+2)=b+1:=by omega
  have hs:2*(s+2) - 2=2*(s+1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]


theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ):
    identityCurveDegree flag a b s w=
      flag.zOnly*(393219+262146*s)+
      flag.yz*(786438+524292*s)+
      flag.all*(1048586+262146*a+524292*b+524292*s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring

def identitySlackZ (b s:ℕ):ℕ:=
  6356732678627780+6993222184206336*b+11231052862266116*s+
    3496611092103168*s ^ 2+6993222184206336*b*s
def identitySlackYZ (a b s:ℕ):ℕ:=
  2223605404022276+6993222184206336*a+6993222184206336*b+
    8475634679195780*s+3496611092103168*s ^ 2+
    6993222184206336*a*s+6993222184206336*b*s
def identitySlackAll (a b s:ℕ):ℕ:=
  2964803968017738+11231052862266116*a+8475634679195780*b+
    3496611092103168*b ^ 2+8475634679195780*s+
    3496611092103168*s ^ 2+6993222184206336*a*b+
    6993222184206336*a*s+6993222184206336*b*s
def identitySlack (flag:FlagDegree) (a b s:ℕ):ℕ:=
  flag.zOnly*identitySlackZ b s+flag.yz*identitySlackYZ a b s+
    flag.all*identitySlackAll a b s


theorem identity_budget_exact (flag:FlagDegree) (a b s:ℕ):
    gap*flagMixed flag (firstTail a b s) (secondTail a b s)=
      (n - w)*(errors+1)*identityCurveDegree flag a b s w+
        identitySlack flag a b s:=by
  rw [identityDegree_linear]
  norm_num [firstTail,secondTail,tail_support_formula,w,n,errors,gap,
    identitySlack,identitySlackZ,identitySlackYZ,identitySlackAll,flagMixed]<;>
    ring

theorem identity_budget (flag:FlagDegree) (a b s:ℕ):
    (n - w)*(errors+1)*identityCurveDegree flag a b s w≤
      gap*flagMixed flag (firstTail a b s) (secondTail a b s):=by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _

theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0<flag.zOnly+flag.yz+flag.all):
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1≤393219+262146*s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1≤786438+524292*s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1≤1048586+262146*a+524292*b+524292*s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega

theorem tangent_gate (a b s:ℕ):
    errors+1≤(secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors+1≤1+2*(b+1)*(w+2)
  have hb:2*(w+2)≤2*(b+1)*(w+2):=by
    have h:=Nat.mul_le_mul_right (w+2)
      (Nat.mul_le_mul_left 2 (show 1≤b+1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors+1≤1+2*(w+2)).trans
    (Nat.add_le_add_left hb 1)

theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s+2≤13) (hY:b+s+3≤60) (hT:a+b+s+3≤1468)
    (hflag:flag.all≤s+2 ∧ flag.yz+flag.all≤b+s+3 ∧
      flag.zOnly+flag.yz+flag.all≤a+b+s+3):
    flag.yz+flag.all<prime ∧ flag.all<prime ∧
      flag.zOnly+flag.yz+flag.all<prime:=by
  dsimp [prime]
  omega

theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s+2≤13) (hY:b+s+3≤60)
    (hfs:flag.all≤s+2) (hfy:flag.yz+flag.all≤b+s+3):
    (1+w*(2*(b+s+3) - 2))*flag.all+
      (flag.yz+flag.all)*((2*(s+2) - 1)*w)<prime:=by
  have hy:2*(b+s+3) - 2≤118:=by omega
  have hs:2*(s+2) - 1≤25:=by omega
  have hfS:flag.all≤13:=hfs.trans hS
  have hfY:flag.yz+flag.all≤60:=hfy.trans hY
  calc
    _≤(1+w*118)*13+60*(25*w):=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _<prime:=by norm_num [w,prime]

theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s+2≤13) (hY:b+s+3≤60)
    (hfs:flag.all≤s+2) (hfy:flag.yz+flag.all≤b+s+3):
    (1+(w+1)*(2*(b+s+3) - 2))*flag.all+
      (flag.yz+flag.all)*((2*(s+2) - 2)*(w+1))<prime:=by
  have hy:2*(b+s+3) - 2≤118:=by omega
  have hs:2*(s+2) - 2≤24:=by omega
  have hfS:flag.all≤13:=hfs.trans hS
  have hfY:flag.yz+flag.all≤60:=hfy.trans hY
  calc
    _≤(1+(w+1)*118)*13+60*(24*(w+1)):=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w+1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w+1) hs))
    _<prime:=by norm_num [w,prime]


def FixedStageBound (a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements+errors →
    (∀ gamma∈Gamma,agreements≤(S.agreementFiber gamma).card) →
    S.F∈RCN174.globalCoefficientBox K weightedCap w (a+b+s+3) (s+2) →
    (flag.all≤s+2 ∧ flag.yz+flag.all≤b+s+3 ∧
      flag.zOnly+flag.yz+flag.all≤a+b+s+3) →
    Gamma.card≤flagMixed flag (firstTail a b s) (secondTail a b s)

theorem fixedStageBound (a b s:ℕ)
    (hS:s+2≤13) (hY:b+s+3≤60) (hT:a+b+s+3≤1468):
    FixedStageBound a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator:S.G∣surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w+1)):=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hprovider:=actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      weightedCap (a+b+s+3) (s+2)
      (by norm_num [w]) (by norm_num [w,weightedCap])
      (by norm_num [weightedCap,prime]) hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
      apply identity_positive
      have hy:0<S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes]<;>norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card*gap≤
        gap*flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card*gap=Gamma.card*(agreements - w):=rfl
        _≤(S.nodes.card - w)*(errors+1)*
            identityCurveDegree flag a b s w:=hinc
        _=(n - w)*(errors+1)*identityCurveDegree flag a b s w:=by
          rw [hnodes]<;>norm_num [n,agreements,errors]
        _≤gap*flagMixed flag (firstTail a b s) (secondTail a b s):=
          identity_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0<gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
      weightedCap (a+b+s+3) (s+2) hnodes hagreement
      (by norm_num [RCN327.w,agreements]) (by norm_num [RCN327.w,weightedCap])
      (by norm_num [weightedCap,prime]) hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some

end
end ProximityPrize.SubmissionLower.LocatorFixedStage
