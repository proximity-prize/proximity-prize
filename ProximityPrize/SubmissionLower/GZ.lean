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
end
end ProximityPrize.SubmissionLower.ContactTwoTailProviderAssembly6732Research
