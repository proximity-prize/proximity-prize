import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedStageBound6734Research
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactInterpolation ContactTranslation
open ContactTaylorNumerators ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFirstTailCertificate6731Research
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research ContactReducedTaylorProfileResearch
open ContactIdentityCurveProvider6731Research ContactFirstTailIdentityIncidence6731Research
open ContactFactoredFlagCount6676Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactProperDelayedTailCertificate6732Research
open ContactTwoTailParameters6734Research
open ContactTwoTailFixedSelectedGeneric6734Research
open ContactTwoTailReducedProviderAssembly6734Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K prime := by
 simpa [prime, ContactParameters6600Research.prime] using
   ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem fixedStageBound_of_numeric
   (a b s : ℕ)
   (hcommonS : (support a b s).s ≤
     ContactProperDelayedTailCertificate6732Research.fixedSupport.s)
   (hcommonYS : (support a b s).ys ≤
     ContactProperDelayedTailCertificate6732Research.fixedSupport.ys)
   (hcommonTotal : (support a b s).total ≤
     ContactProperDelayedTailCertificate6732Research.fixedSupport.total)
   (hsupportChar : a + b + s + 3 < prime)
   (hidentityMixed : ∀ flag : FlagDegree,
     (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
       flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
     (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
       (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime)
   (hproviderMixed : ∀ flag : FlagDegree,
     (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
       flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
     (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
       (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime)
   (htangentGate : errors + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz)
   (hidentityBudget : ∀ flag : FlagDegree,
     (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
       gap * flagMixed flag (firstTail a b s) (secondTail a b s))
   (hidentityPositive : ∀ flag : FlagDegree,
     0 < flag.zOnly + flag.yz + flag.all →
       1 ≤ identityCurveDegree flag a b s w) :
   FixedStageBound a b s := by
 intro Gamma flag S hnodes hagreement hbox hflag
 by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
 · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
       (numerator K S.F (w + 1)) :=
     (globalTailCut_dvd_iff (polynomialEmbedding K)
       (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
   have hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
       flag.zOnly + flag.yz + flag.all < prime := by
     omega
   have hprovider := actual_identityCurveCountProvider S agreements hnodes
     hagreement (by norm_num [agreements, errors, n, w]) hTailNumerator
     (41 * agreements) (a + b + s + 3) (s + 2)
     (by norm_num [w]) (by norm_num [agreements, errors, n, w])
     (by norm_num [prime, agreements, errors, n]) hbox hflagChar
     (hidentityMixed flag hflag)
   let identityDegree := identityCurveDegree flag a b s w
   have hpositive : 1 ≤ identityDegree := by
     apply hidentityPositive flag
     have hy : 0 < S.G.degreeOf 1 := S.y_dependent
     have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
     omega
   have hinc := identity_surface_seed_bound S agreements identityDegree hprovider
     hagreement (by norm_num [agreements, errors, n, w])
     (by rw [hnodes]; norm_num [agreements, errors, n]) hpositive
   have hbudget := hidentityBudget flag
   have hscaled : Gamma.card * gap ≤
       gap * flagMixed flag (firstTail a b s) (secondTail a b s) := by
     calc
       Gamma.card * gap = Gamma.card * (agreements - w) := rfl
       _ ≤ (S.nodes.card - w) * (errors + 1) * identityDegree := hinc
       _ = (n - w) * (errors + 1) * identityDegree := by
         rw [hnodes]
         norm_num [n, agreements, errors]
       _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) := hbudget
   apply Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < gap)
   simpa only [Nat.mul_comm] using hscaled
 · have hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
       flag.zOnly + flag.yz + flag.all < prime := by
     omega
   have hprovider := exists_delayedTailMultiplicityProvider_of_reduced S
     hcommonS hcommonYS hcommonTotal hTail hflagChar
     (hproviderMixed flag hflag)
     (41 * agreements) (a + b + s + 3) (s + 2) hnodes hagreement
     (by norm_num [agreements, errors, n, w])
     (by norm_num [prime, agreements, errors, n]) hbox htangentGate
   exact stage_card_le_flagMixed S hprovider.some
end
end ProximityPrize.SubmissionLower.ContactTwoTailFixedStageBound6734Research
