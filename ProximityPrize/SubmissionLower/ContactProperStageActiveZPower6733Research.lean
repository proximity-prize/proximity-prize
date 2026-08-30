import ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6733Research
import ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6733Research
import ProximityPrize.SubmissionLower.ContactActiveNestedFixedPowers6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveZPower6733Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperCutSeedCount ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6733Research
open ContactProperStageIndexedPower6733Research
open ContactProperStageActiveFamilies6733Research
open ContactActiveNestedFlagData6733Research
open ContactActiveNestedFixedPowers6733Research
open ContactFlagPlaneResultantBounds6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactWeakSeparableSeparatorResearch
open ContactFlagTriangularProjectionResearch
open ContactFlagBezout6543Research
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
theorem properStage_activeZFixedPowers
    (S:Stage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (base:∀ C:StageComponent S,SeparableLiteralCoordinate C.1)
    (hactive:∀ C:StageComponent S,
      KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 0)≠0∨
        KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 2)≠0)
    (hZ:∀ C:StageComponent S,LiteralProjectionGate C 2)
    (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G≠0)
    (D:AdaptiveNestedProjectionDataActive base hactive hSderiv):
    ActiveNestedZFixedPowers base hactive hZ hSderiv D
      (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)):=by
  intro q hq hqMonic a₀
  let F:=activeStageZFamily S base hactive hZ hSderiv D
  let W:StageIndexedFactor S (ActiveStageZIndex S) F:=
    { q:=q,irreducible:=hq,monic:=hqMonic,witness:=a₀}
  have hp:=properStage_indexedFixedFactor_groupedPowerDvd S hfirstProper F W
  change q^stageFamilyGroupedExponent S (ActiveStageZIndex S)
      hfirstProper F q∣stageFamilyResultant S (ActiveStageZIndex S) F
  exact hp
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveZPower6733Research
