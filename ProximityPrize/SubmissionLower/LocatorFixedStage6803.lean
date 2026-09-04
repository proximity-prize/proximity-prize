import ProximityPrize.SubmissionLower.LocatorFixedStage
import ProximityPrize.SubmissionLower.LocatorHybridGatesC26803

/-!
# Padded fixed stage at agreement 181363

This is the ordinary (non-hybrid) half of the 68.03 own-bound.  It keeps the
same two reduced tails as the 68.02 C2 argument, but uses error cap `80781`,
gap `50292`, the wider `(middle,total) = (135,6676)` box, and weighted cap
`17773574 = 98 * 181363`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedStage6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN087 RCN095 RCN135 RCN136 RCN146 RCN159 RCN174
  RCN198 RCN203 RCN263 RCN275 RCN313 RCN335
open LocatorHybridGatesC26803

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80781
def agreements : ℕ := 181363
def gap : ℕ := 50292
def prime : ℕ := 2130706433
def weightedCap : ℕ := 17773574

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, RCN223.prime] using
    RCN128.challenge_field_characteristic6600

def firstTail (a b s : ℕ) : FlagDegree :=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)

def secondTail (a b s : ℕ) : FlagDegree :=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)

theorem tail_support_formula (a b s d : ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d =
      ⟨2 * a * d, 1 + 2 * (b + 1) * d, 2 * (s + 1) * d⟩ :=
  LocatorFixedStage.tail_support_formula a b s d

theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simpa only [w, LocatorFixedStage.w] using
    LocatorFixedStage.identityDegree_linear flag a b s

def identitySlackZ (b s : ℕ) : ℕ :=
  6204689135031870 + 6912132582998016 * b + 11048600795550156 * s +
    3456066291499008 * s ^ 2 + 6912132582998016 * b * s

def identitySlackYZ (a b s : ℕ) : ℕ :=
  2041153027974036 + 6912132582998016 * a + 6912132582998016 * b +
    8272910057511600 * s + 3456066291499008 * s ^ 2 +
    6912132582998016 * a * s + 6912132582998016 * b * s

def identitySlackAll (a b s : ℕ) : ℕ :=
  2721533772399288 + 11048600795550156 * a + 8272910057511600 * b +
    3456066291499008 * b ^ 2 + 8272910057511600 * s +
    3456066291499008 * s ^ 2 + 6912132582998016 * a * b +
    6912132582998016 * a * s + 6912132582998016 * b * s

def identitySlack (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * identitySlackZ b s + flag.yz * identitySlackYZ a b s +
    flag.all * identitySlackAll a b s

theorem identity_budget_exact (flag : FlagDegree) (a b s : ℕ) :
    gap * flagMixed flag (firstTail a b s) (secondTail a b s) =
      (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
        identitySlack flag a b s := by
  rw [identityDegree_linear]
  norm_num [firstTail, secondTail, tail_support_formula, w, n, errors, gap,
    identitySlack, identitySlackZ, identitySlackYZ, identitySlackAll,
    flagMixed] <;> ring

theorem identity_budget (flag : FlagDegree) (a b s : ℕ) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * flagMixed flag (firstTail a b s) (secondTail a b s) := by
  rw [identity_budget_exact]
  exact Nat.le_add_right _ _

theorem identity_positive (flag : FlagDegree) (a b s : ℕ)
    (hpos : 0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w := by
  simpa only [w, LocatorFixedStage.w] using
    LocatorFixedStage.identity_positive flag a b s hpos

theorem tangent_gate (a b s : ℕ) :
    errors + 1 ≤ (secondTail a b s).yz := by
  rw [secondTail, tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb : 2 * (w + 2) ≤ 2 * (b + 1) * (w + 2) := by
    have h := Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors, w] : errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)

def FixedStageBound (D a b s : ℕ) : Prop :=
  ∀ {Gamma : Finset K} {flag : FlagDegree},
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card = agreements + errors →
    (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w
      (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)

theorem fixedStageBound (D a b s : ℕ)
    (hDlow : w + 1 ≤ D) (hDhigh : D ≤ weightedCap)
    (hS : s + 2 ≤ 29) (hY : b + s + 3 ≤ 135)
    (hT : a + b + s + 3 ≤ 6676) :
    FixedStageBound D a b s := by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar : D < prime :=
    hDhigh.trans_lt (by norm_num [weightedCap, prime])
  have hflagChar := flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail :
      S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider := actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements, w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive : 1 ≤ identityCurveDegree flag a b s w := by
      apply identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements, w])
      (by rw [hnodes] <;> norm_num [agreements, errors]) hpositive
    have hscaled : Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s) := by
      calc
        Gamma.card * gap = Gamma.card * (agreements - w) := rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            identityCurveDegree flag a b s w := hinc
        _ = (n - w) * (errors + 1) *
            identityCurveDegree flag a b s w := by
          rw [hnodes] <;> norm_num [n, agreements, errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          identity_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap] : 0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider := exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap := errors) agreements S hTail hflagChar
      (reduced_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w, agreements])
      (by simpa only [RCN327.w, w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some

end

end ProximityPrize.SubmissionLower.LocatorFixedStage6803
