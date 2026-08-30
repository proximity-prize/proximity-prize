import ProximityPrize.SubmissionLower.GM
import ProximityPrize.SubmissionLower.AM
namespace ProximityPrize.SubmissionLower.ContactTwoTailProviderAssembly6732Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch ContactAdaptiveUnitPoleFamilyResearch
open ContactWeakSeparableSeparatorResearch ActualCurveCoordinateField
open CoordinateBoxZeroCount
open ContactTangentCoefficientProvider6732Research
open ContactTwoTailResultantProvider6732Research
open ContactInterpolation
open ContactAdaptiveProjectionCoordinateResearch
open ContactTwoTailTangentCost6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p:ℕ}
variable [CharP (Omega K) p] {flag:FlagDegree}
variable {support:ContactResidualSupportParametersResearch.ResidualSupportParameters}
abbrev FixedStage
   (phi:Polynomial K →+*Omega K:=polynomialEmbedding K):=
 ResidualStage phi Gamma x p ContactTwoTailParameters6733Research.errors
   flag ContactTwoTailParameters6733Research.w support
structure ProperDelayedTailCertificate
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (B:PrimeFlagBudgetFamily
     (G:=S.G)
     (T:=globalTailCut (polynomialEmbedding K) S.F
       (ContactTwoTailParameters6733Research.w+1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag
     (ContactTwoTailParameters6733Research.tailFlag
       (ContactTwoTailParameters6733Research.w+1)))
   (multiplicity:FirstTailComponent S → ℕ) where
 branch:∀ C:FirstTailComponent S,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut (polynomialEmbedding K) S.F
       (ContactTwoTailParameters6733Research.w+1+delay)∉C.1∧
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (ContactTwoTailParameters6733Research.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         multiplicity C*B.weightedCost
           (ContactTwoTailParameters6733Research.tailFlag
             (ContactTwoTailParameters6733Research.w+2)) C)∨
   (∀ delay,globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1+delay)∈C.1)
theorem delayedTailMultiplicityProvider_of_certificates
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1))
   (baseFamily:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
   (U:AdaptiveUnitProjectionFamily baseFamily flag
     (ContactTwoTailParameters6733Research.tailFlag
       (ContactTwoTailParameters6733Research.w+1)))
   (hyzTranscendental:∀ C:FirstTailComponent S,
     Transcendental (Omega K)
       (coordinateValue (Omega K) (CoordinateField (Omega K) C.1)
         (U.yzProjection C)))
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=ContactTwoTailParameters6733Research.agreements+
     ContactTwoTailParameters6733Research.errors)
   (hagreement:∀ gamma∈Gamma,
     ContactTwoTailParameters6733Research.agreements ≤
       (S.agreementFiber gamma).card)
   (hshort:ContactTwoTailParameters6733Research.w+1 ≤ bound)
   (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound
     ContactTwoTailParameters6733Research.w seedCap slopeCap)
   (multiplicity:FirstTailComponent S → ℕ)
   (hone:∀ C,1 ≤ multiplicity C)
   (proper:ProperDelayedTailCertificate S U.toPrimeFlagBudgetFamily multiplicity)
   (resultants:RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity):
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=ContactTwoTailParameters6733Research.tailFlag
       (ContactTwoTailParameters6733Research.w+1))
     (tailFlag2:=ContactTwoTailParameters6733Research.tailFlag
       (ContactTwoTailParameters6733Research.w+2)) S):=by
 let B:=U.toPrimeFlagBudgetFamily
 let secondTail:=ContactTwoTailParameters6733Research.tailFlag
   (ContactTwoTailParameters6733Research.w+2)
 let cost:FirstTailComponent S → ℕ:=
   fun C => multiplicity C*B.weightedCost secondTail C
 have hyzPositive (C:FirstTailComponent S):1 ≤ B.yzCost C:=by
   change 1 ≤ coordinateDegree (Omega K) (CoordinateField (Omega K) C.1)
     (U.yzProjection C)
   exact one_le_coordinateDegree_of_transcendental_value
     (U.yzProjection C) (hyzTranscendental C)
 have hyzPole (C:FirstTailComponent S):∀ W:Finset
     (CoordinatePoleMass.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,ContactSparsePoleSupportResearch.exponentSetPoleWeight
       v.val (coordinate (Omega K) C.1)
       (ContactFlagBezout6543Research.flagSupport
         ContactFlagBezout6543Research.unitYZFlag)) ≤ (B.yzCost C:ℤ):=by
   exact U.toAdaptiveUnitPoleBudget.yzPole C
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (ContactTwoTailParameters6733Research.w+1+delay)∈C.1):
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (ContactTwoTailParameters6733Research.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (ContactTwoTailParameters6733Research.errors+1)*B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper (baseFamily C)
     ContactTwoTailParameters6733Research.agreements bound seedCap slopeCap
     hnodes hagreement (by decide) (by decide) hshort hchar hbox B
     (hyzPositive C) hall (hyzPole C)
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=cost
   one_le_multiplicity:=hone
   tangentYZGate:=errors_succ_le_secondTail_yz
   cost_le:=fun C => le_rfl
   divisor_le:=resultants.divisor_le B multiplicity
   componentBound:=?_
   dichotomy:=?_}⟩
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact hproper.choose_spec.2.2.2
   · exact (tangentCount C htangent).trans
       (tangentCost_le_multiplicity_secondTail_weightedCost
         B C (multiplicity C) (hone C))
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact Or.inl ⟨hproper.choose,hproper.choose_spec.1,
       hproper.choose_spec.2.1,hproper.choose_spec.2.2.1⟩
   · exact Or.inr ⟨htangent,tangentCount C htangent⟩
end
end ProximityPrize.SubmissionLower.ContactTwoTailProviderAssembly6732Research
