import ProximityPrize.SubmissionLower.ContactAnchoredReducedWeightedResultants6750Research
import ProximityPrize.SubmissionLower.ContactTangentCoefficientProvider6732Research

 








namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredReducedDelayedTailAssembly6750Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactIdentityResidualIterationResearch
open ContactRegularComponentCover ContactFlagBezout6543Research
open ContactMovingAgreementCertificate6719Research
open ContactFirstTailCertificate6731Research ContactProperCutSeedCount
open ContactDelayedTailMultiplicityProvider6732Research
open ContactPrimeSeedIncidence ContactInterpolation
open ContactResidualSupportParametersResearch
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
open ContactAnchoredReducedWeightedResultants6750Research
open ContactAnchoredReducedActiveGeometry6750Research
open ContactAnchoredCongruentCuts6750Research
open ContactTangentCoefficientProvider6732Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactAdaptiveProjectionCoordinateResearch
open ContactWeakSeparableSeparatorResearch
open ContactFlagAffineFamilyDegree6543Research
open ContactPrimeFlagBudgetFamilyResearch
open ActualCurveCoordinateField CoordinateBoxZeroCount

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : Nat} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {a b s : Nat}

 


theorem exists_delayedTailMultiplicityProvider_of_reducedWeightedResultants
    (S : ResidualStage (polynomialEmbedding K) Gamma x p anchoredErrors flag
      anchoredW (support a b s))
    (hs : (support a b s).s ≤ anchoredFixedSupport.s)
    (hys : (support a b s).ys ≤ anchoredFixedSupport.ys)
    (htotal : (support a b s).total ≤ anchoredFixedSupport.total)
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (anchoredW + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixed : (1 + (anchoredW + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (anchoredW + 1)) < p)
    (htangentGate : anchoredErrors + 1 ≤
      (reducedResidualAgreementFlag6750 (support a b s)
        (anchoredW + 2)).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (anchoredW + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (anchoredW + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (anchoredErrors + 1) *
            (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C) :
    Nonempty (DelayedTailMultiplicityProvider
      (tailFlag1 := reducedResidualAgreementFlag6750 (support a b s)
        (anchoredW + 1))
      (tailFlag2 := reducedResidualAgreementFlag6750 (support a b s)
        (anchoredW + 2)) S) := by
  apply exists_delayedTailMultiplicityProvider_of_anchoredDVR_reduced
    S hs hys htotal hfirstProper
      (reducedBudgetFamily S hfirstProper hflagChar hmixed)
      htangentGate htangent
  exact transportedWeightedResultants S hs hys htotal hfirstProper
    hflagChar hmixed

end

end ContactAnchoredReducedDelayedTailAssembly6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredReducedDelayedTailAssembly6750Research.exists_delayedTailMultiplicityProvider_of_reducedWeightedResultants
