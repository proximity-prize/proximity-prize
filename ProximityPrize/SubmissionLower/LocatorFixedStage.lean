import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ
namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN146 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80408
def agreements:ℕ:=181736
def gap:ℕ:=50665
def prime:ℕ:=2130706433
def weightedCap:ℕ:=10358952
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
    identityCurveDegree flag a b s w=
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
  simp only [identityCurveDegree,paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all,w]
  ring
def identitySlackZ (b s:ℕ):ℕ:=
  6300811578695047 + 6963397703761920 * b + 11163947610609568 * s +
    3481698851880960 * s ^ 2 + 6963397703761920 * b * s
def identitySlackYZ (a b s:ℕ):ℕ:=
  2156500038594364 + 6963397703761920 * a + 6963397703761920 * b +
    8401073250542446 * s + 3481698851880960 * s ^ 2 +
    6963397703761920 * a * s + 6963397703761920 * b * s
def identitySlackAll (a b s:ℕ):ℕ:=
  2875330014714003 + 11163947610609568 * a + 8401073250542446 * b +
    3481698851880960 * b ^ 2 + 8401073250542446 * s +
    3481698851880960 * s ^ 2 + 6963397703761920 * a * b +
    6963397703761920 * a * s + 6963397703761920 * b * s
def identitySlack (flag:FlagDegree) (a b s:ℕ):ℕ:=
  flag.zOnly * identitySlackZ b s + flag.yz * identitySlackYZ a b s +
    flag.all * identitySlackAll a b s
theorem identity_budget_exact (flag:FlagDegree) (a b s:ℕ) :
    gap * flagMixed flag (firstTail a b s) (secondTail a b s) =
      (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
        identitySlack flag a b s:=by
  rw [identityDegree_linear]
  norm_num [firstTail,secondTail,tail_support_formula,w,n,errors,gap,
    identitySlack,identitySlackZ,identitySlackYZ,identitySlackAll,flagMixed] <;>
    ring
theorem identity_budget (flag:FlagDegree) (a b s:ℕ) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
    (hpos:0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w:=by
  rw [identityDegree_linear]
  have hz:=Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy:=Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha:=Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega
theorem tangent_gate (a b s:ℕ) :
    errors + 1 ≤ (secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
    have h:=Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 16) (hY:b + s + 3 ≤ 75) (hT:a + b + s + 3 ≤ 2319)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 16) (hY:b + s + 3 ≤ 75)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 148:=by omega
  have hs:2 * (s + 2) - 1 ≤ 31:=by omega
  have hfS:flag.all ≤ 16:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 75:=hfy.trans hY
  calc
    _ ≤ (1 + w * 148) * 16 + 75 * (31 * w) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _ < prime:=by norm_num [w,prime]
theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 16) (hY:b + s + 3 ≤ 75)
    (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime:=by
  have hy:2 * (b + s + 3) - 2 ≤ 148:=by omega
  have hs:2 * (s + 2) - 2 ≤ 30:=by omega
  have hfS:flag.all ≤ 16:=hfs.trans hS
  have hfY:flag.yz + flag.all ≤ 75:=hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 148) * 16 + 75 * (30 * (w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
    _ < prime:=by norm_num [w,prime]
def FixedStageBound (D a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements + errors →
    (∀ gamma ∈ Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (D a b s:ℕ)
    (hDlow:w + 1 ≤ D) (hDhigh:D ≤ weightedCap)
    (hS:s + 2 ≤ 16) (hY:b + s + 3 ≤ 75) (hT:a + b + s + 3 ≤ 2319) :
    FixedStageBound D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D < prime:=hDhigh.trans_lt (by norm_num [weightedCap,prime])
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider:=actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
      apply identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes] <;> norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card * gap=Gamma.card * (agreements - w):=rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            identityCurveDegree flag a b s w:=hinc
        _= (n - w) * (errors + 1) * identityCurveDegree flag a b s w:=by
          rw [hnodes] <;> norm_num [n,agreements,errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          identity_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some
end
end ProximityPrize.SubmissionLower.LocatorFixedStage
