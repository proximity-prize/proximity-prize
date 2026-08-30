import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.O0
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.FQ
import ProximityPrize.SubmissionLower.AL
namespace ProximityPrize.SubmissionLower.ContactTwoTailFixedSelectedGeneric6734Research
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactFactorCaps
open ContactGenericInitialPoint ContactFlagBezout6543Research
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactRegularFactorFlag6600Research
open ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorResidualStage6600Research
open ContactGlobalSelectedFamilies6600Research ContactResidualSupportParametersResearch
open ContactIdentityResidualIterationResearch ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactFactoredFlagCount6676Research ContactGeometricFactorCover
open ContactProfileFixedSelectedCombinerResearch ContactTightSingularLedgerResearch
open ContactMovingAgreementCertificate6719Research ContactMovingPositiveLedger6719Research
open ContactReducedTaylorProfileResearch ContactTwoTailParameters6734Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K prime := by
 simpa [prime, ContactParameters6600Research.prime] using
   ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def fixedProfile (a b s : ℕ) : ContactRobustFixedMeet6656Research.Profile :=
 ⟨n, w, agreements, 41 * agreements, a + b + s + 3, s + 2⟩
def fixedTightProfile (a b s : ℕ) : TightParameters :=
 ⟨n, w, agreements, 41 * agreements, a + b + s + 3, s + 2⟩
def fixedAlignment (a b s : ℕ) :
   FixedParameterAlignment (fixedProfile a b s) (fixedTightProfile a b s) where
 n := rfl
 w := rfl
 agreements := rfl
 weightedCap := rfl
 seedTotalCap := rfl
 slopeCap := rfl
def fixedFlag (a b s : ℕ) : FlagDegree := surfaceFlag a b s
def firstTail (a b s : ℕ) : FlagDegree :=
 reducedResidualAgreementFlag (support a b s) (w + 1)
def secondTail (a b s : ℕ) : FlagDegree :=
 reducedResidualAgreementFlag (support a b s) (w + 2)
def fixedRegularCost (a b s : ℕ) : ℕ :=
 flagMixed (fixedFlag a b s) (firstTail a b s) (secondTail a b s)
theorem support_of_dvd
   (a b s : ℕ) (F Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (hdiv : F ∣ Q)
   (Hsupport : ResidualSupportData (support a b s) Q) :
   ResidualSupportData (support a b s) F :=
 ⟨(weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans
     Hsupport.s_weight,
   (weightedTotalDegree_le_of_dvd residualYSWeights F Q hdiv hQ).trans
     Hsupport.ys_weight,
   (weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans
     Hsupport.total_weight⟩
def fixedGeometricStage
   (a b s : ℕ) (hsSmall : s + 2 < prime)
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ globalCoefficientBox K (41 * agreements) w
     (a + b + s + 3) (s + 2))
   (Hsupport : ResidualSupportData (support a b s) Q)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (u0 u1 : I → K)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (R : RegularIndex Q) (g : GeometricFactor K R.1) :
   letI : CharP (GenericField K) prime := genericField_charP K prime
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     IRSProfile.domain prime errors (geometricCumulativeFlag K g) w
     (support a b s) := by
 letI : CharP (GenericField K) prime := genericField_charP K prime
 have hRdata := directFactor_data Q R.1 hQ (41 * agreements) w
   (a + b + s + 3) (s + 2) hbox R.2
 have hRsmall : R.1.degreeOf (2 : Fin 4) < prime :=
   (degreeOf_R_le_of_mem_box R.1 (41 * agreements) w
     (a + b + s + 3) (s + 2) hRdata.2.2).trans_lt hsSmall
 have hsupport : ResidualSupportData (support a b s) R.1 :=
   support_of_dvd a b s R.1 Q hQ
     (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1 Hsupport
 let S := regularGeometricResidualStageOfSupport (support a b s) Q selected Gamma
   (Finset.univ : Finset I) IRSProfile.domain u0 u1
   IRSProfile.domain.injective.injOn hdegree hnoPencil R
   hRdata.1 hRdata.2.1 hRsmall hsupport (by norm_num [w, prime]) g
 exact reflagResidualStage S (polynomialIn_surfaceCumulativeFlag g.1)
theorem geometric_flag_caps
   (a b s : ℕ)
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ globalCoefficientBox K (41 * agreements) w
     (a + b + s + 3) (s + 2))
   (Hsupport : ResidualSupportData (support a b s) Q)
   (R : RegularIndex Q) (g : GeometricFactor K R.1) :
   (geometricCumulativeFlag K g).all ≤ s + 2 ∧
     (geometricCumulativeFlag K g).yz +
       (geometricCumulativeFlag K g).all ≤ b + s + 3 ∧
     (geometricCumulativeFlag K g).zOnly +
       (geometricCumulativeFlag K g).yz +
       (geometricCumulativeFlag K g).all ≤ a + b + s + 3 := by
 have hRdata := directFactor_data Q R.1 hQ (41 * agreements) w
   (a + b + s + 3) (s + 2) hbox R.2
 simpa only [ContactMovingAgreementCertificate6719Research.support] using
   geometricCumulativeFlag_le_support R.1 hRdata.1.ne_zero
     (support_of_dvd a b s R.1 Q hQ
       (ContactImplicitContactLift.positiveRFactors_spec Q R.1 R.2).2.1
       Hsupport) g
def FixedStageBound (a b s : ℕ) : Prop :=
 ∀ {Gamma : Finset K} {flag : FlagDegree},
   (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (support a b s)) →
   S.nodes.card = agreements + errors →
   (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
   S.F ∈ globalCoefficientBox K (41 * agreements) w
     (a + b + s + 3) (s + 2) →
   (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
     flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
   Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem regular_factor_seed_bound
   (a b s : ℕ) (hsSmall : s + 2 < prime)
   (stageBound : FixedStageBound a b s)
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ globalCoefficientBox K (41 * agreements) w
     (a + b + s + 3) (s + 2))
   (Hsupport : ResidualSupportData (support a b s) Q)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (u0 u1 : I → K)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
   (R : RegularIndex Q) :
   (regularSeeds Q selected Gamma R).card ≤
     flagMixed (regularCumulativeFlag Q R) (firstTail a b s) (secondTail a b s) := by
 letI : CharP (GenericField K) prime := genericField_charP K prime
 have hRdata := directFactor_data Q R.1 hQ (41 * agreements) w
   (a + b + s + 3) (s + 2) hbox R.2
 have hsolutions : ∀ gamma ∈ regularSeeds Q selected Gamma R,
     specialization K (selected gamma) gamma R.1 = 0 := by
   intro gamma hgamma
   exact (Finset.mem_filter.mp hgamma).2.1
 have hcover := card_le_sum_geometricSeeds K R.1 hRdata.1.ne_zero selected
   (regularSeeds Q selected Gamma R) hsolutions
 have hstage : ∀ g : GeometricFactor K R.1,
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card ≤
       flagMixed (geometricCumulativeFlag K g) (firstTail a b s) (secondTail a b s) := by
   intro g
   let S := fixedGeometricStage a b s hsSmall Q hQ hbox Hsupport selected Gamma
     u0 u1 hdegree hnoPencil R g
   have hsub : geometricSeeds K R.1 selected
       (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
     (geometricSeeds_subset K R.1 selected
       (regularSeeds Q selected Gamma R) g).trans
         (regularSeeds_subset Q selected Gamma R)
   have hnodesS : S.nodes.card = agreements + errors := by
     change (Finset.univ : Finset I).card = agreements + errors
     norm_num [I, agreements, errors, n]
   have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
       (regularSeeds Q selected Gamma R) g,
       agreements ≤ (S.agreementFiber gamma).card := by
     intro gamma hgamma
     simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
       fixedGeometricStage, reflagResidualStage,
       regularGeometricResidualStageOfSupport,
       geometricResidualStageOfSupport] using
         hagreement gamma (hsub hgamma)
   have hflag := geometric_flag_caps a b s Q hQ hbox Hsupport R g
   have hboxS : S.F ∈ globalCoefficientBox K (41 * agreements) w
       (a + b + s + 3) (s + 2) := by
     change R.1 ∈ globalCoefficientBox K (41 * agreements) w
       (a + b + s + 3) (s + 2)
     simpa only using hRdata.2.2
   exact stageBound S hnodesS hagreementS hboxS hflag
 calc
   (regularSeeds Q selected Gamma R).card ≤
       ∑ g : GeometricFactor K R.1,
         (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card := hcover
   _ ≤ ∑ g : GeometricFactor K R.1,
       flagMixed (geometricCumulativeFlag K g) (firstTail a b s) (secondTail a b s) :=
     Finset.sum_le_sum (fun g _ => hstage g)
   _ ≤ flagMixed (originalCumulativeFlag R.1) (firstTail a b s) (secondTail a b s) := by
     have hc := geometricCumulativeFlag_budgets R.1 hRdata.1.ne_zero
     exact sum_flagMixed_le_of_cumulative (geometricCumulativeFlag K)
       (originalCumulativeFlag R.1) _ _ hc.1 hc.2.1 hc.2.2
theorem fixed_count_le
   (a b s : ℕ) (hsSmall : s + 2 < prime)
   (stageBound : FixedStageBound a b s)
   (hseedSmall : (2 * (s + 2) - 1) * (a + b + s + 3) < prime)
   (himplicitYSmall : (fixedTightProfile a b s).implicitYCap < prime)
   (hmixedSmall : 2 * (fixedTightProfile a b s).implicitYCap *
     (fixedTightProfile a b s).algebraicCap < prime)
   (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
   (hbox : Q ∈ globalCoefficientBox K (41 * agreements) w
     (a + b + s + 3) (s + 2))
   (Hsupport : ResidualSupportData (support a b s) Q)
   (selected : K → Polynomial K) (Gamma : Finset K)
   (u0 u1 : I → K)
   (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma Q = 0)
   (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤
     ((Finset.univ : Finset I).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
   (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
   Gamma.card ≤ fixedRegularCost a b s + (fixedTightProfile a b s).countCap := by
 let nodes : Finset I := Finset.univ
 have hinj : Set.InjOn IRSProfile.domain nodes := IRSProfile.domain.injective.injOn
 have hnodes : nodes.card = (fixedProfile a b s).n := by
   change Fintype.card I = n
   norm_num [I, IRSProfile.Index, n]
 have hdegreeP : ∀ gamma ∈ Gamma,
     (selected gamma).natDegree ≤ (fixedProfile a b s).w := by
   simpa only [fixedProfile] using hdegree
 have hagreementP : ∀ gamma ∈ Gamma, (fixedProfile a b s).agreements ≤
     (nodes.filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card := by
   simpa only [fixedProfile, nodes] using hagreement
 have hnoPencilP : NoLargeSelectedPencil selected Gamma
     (fixedProfile a b s).w (fixedProfile a b s).errors := by
   simpa [fixedProfile, ContactRobustFixedMeet6656Research.Profile.errors,
     errors, agreements, n] using hnoPencil
 have h := global_count_le_regular_div_add_tight_countCap
   (fixedProfile a b s) (fixedTightProfile a b s) (fixedAlignment a b s)
   (prime := prime) (regularNumerator := fixedRegularCost a b s * gap ^ 2)
   Q hQ hbox
   (by simp [fixedProfile]) hsSmall (by norm_num [fixedProfile, w])
   (by norm_num [fixedProfile, w, prime])
   (by simp [fixedProfile, agreements, errors, n, w]; omega)
   (by
     change 1 ≤ (2 * (s + 2) - 1) * (a + b + s + 3)
     exact Nat.mul_pos (by omega) (by omega))
   (by simpa only [fixedProfile] using hseedSmall)
   himplicitYSmall hmixedSmall
   (by norm_num [fixedProfile, agreements, errors, n, w])
   (by norm_num [fixedProfile, agreements, errors, n, w])
   selected Gamma nodes IRSProfile.domain u0 u1 hinj hnodes hdegreeP hsolution
   hagreementP hnoPencilP
   (fun R : ContactRegularFactorFlag6600Research.RegularIndex Q =>
     regularCumulativeFlag Q R)
   (fun f => flagMixed f (firstTail a b s) (secondTail a b s) * gap ^ 2)
   (fun count hcount => by
     have hc := regularCumulativeFlag_budgets Q hQ Hsupport
     calc
       (∑ R, count R) * gap ^ 2 = ∑ R, count R * gap ^ 2 := by
         rw [Finset.sum_mul]
       _ ≤ ∑ R, flagMixed (regularCumulativeFlag Q R)
             (firstTail a b s) (secondTail a b s) * gap ^ 2 :=
         Finset.sum_le_sum (fun R _ => hcount R)
       _ = (∑ R, flagMixed (regularCumulativeFlag Q R)
             (firstTail a b s) (secondTail a b s)) * gap ^ 2 := by
         rw [Finset.sum_mul]
       _ ≤ fixedRegularCost a b s * gap ^ 2 := Nat.mul_le_mul_right _ (by
         change (∑ R, flagMixed (regularCumulativeFlag Q R)
           (firstTail a b s) (secondTail a b s)) ≤
             flagMixed (fixedFlag a b s) (firstTail a b s) (secondTail a b s)
         apply sum_flagMixed_le_of_cumulative (regularCumulativeFlag Q)
           (fixedFlag a b s) _ _
         · simpa [fixedFlag, surfaceFlag,
             ContactMovingAgreementCertificate6719Research.support] using hc.1
         · change (∑ R : ContactRegularFactorFlag6600Research.RegularIndex Q,
               ((regularCumulativeFlag Q R).yz +
               (regularCumulativeFlag Q R).all)) ≤ b + 1 + (s + 2)
           have hcy := hc.2.1
           change (∑ R : ContactRegularFactorFlag6600Research.RegularIndex Q,
               ((regularCumulativeFlag Q R).yz +
               (regularCumulativeFlag Q R).all)) ≤ b + s + 3 at hcy
           exact hcy.trans_eq (by omega)
         · change (∑ R : ContactRegularFactorFlag6600Research.RegularIndex Q,
               ((regularCumulativeFlag Q R).zOnly +
               (regularCumulativeFlag Q R).yz +
               (regularCumulativeFlag Q R).all)) ≤ a + (b + 1) + (s + 2)
           have hct := hc.2.2
           change (∑ R : ContactRegularFactorFlag6600Research.RegularIndex Q,
               ((regularCumulativeFlag Q R).zOnly +
               (regularCumulativeFlag Q R).yz +
               (regularCumulativeFlag Q R).all)) ≤ a + b + s + 3 at hct
           exact hct.trans_eq (by omega)))
   (fun R => by
     have hr := regular_factor_seed_bound a b s hsSmall stageBound Q hQ hbox
       Hsupport selected Gamma u0 u1 hdegree hagreement hnoPencil R
     change (regularSeeds Q selected Gamma R).card * gap ^ 2 ≤
       flagMixed (regularCumulativeFlag Q R) (firstTail a b s)
         (secondTail a b s) * gap ^ 2
     exact Nat.mul_le_mul_right (gap ^ 2) hr)
 have hgap : (fixedProfile a b s).gap = gap := by
   simp [fixedProfile, ContactRobustFixedMeet6656Research.Profile.gap,
     gap, agreements, errors, n, w]
 simpa only [hgap, Nat.mul_div_left _ (pow_pos (by decide : 0 < gap) 2)] using h
end
end ProximityPrize.SubmissionLower.ContactTwoTailFixedSelectedGeneric6734Research
