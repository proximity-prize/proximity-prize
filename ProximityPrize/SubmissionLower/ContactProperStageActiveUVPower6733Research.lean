import ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6733Research
import ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6733Research
import ProximityPrize.SubmissionLower.ContactActiveNestedFixedPowers6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveUVPower6733Research
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
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactWeakSeparableSeparatorResearch
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
variable (S:Stage K I Gamma x p flag)
variable (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
  (ContactTwoTailParameters6733Research.w+1))
variable (base:∀ C:StageComponent S,SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:StageComponent S,
  KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
      (coordinate (GenericField K) C.1 0)≠0∨
    KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
      (coordinate (GenericField K) C.1 2)≠0)
variable (hZ:∀ C:StageComponent S,LiteralProjectionGate C 2)
variable (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G≠0)
variable (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
theorem properStage_activeUFixedPowers:
    ActiveNestedUFixedPowers base hactive hSderiv D
      (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)):=by
  intro q hq hqMonic C₀
  let F:=activeStageUFamily S base hactive hSderiv D
  let W:StageIndexedFactor S (StageComponent S) F:=
    { q:=q,irreducible:=hq,monic:=hqMonic,witness:=C₀}
  have hp:=properStage_indexedFixedFactor_groupedPowerDvd S hfirstProper F W
  change q^stageFamilyGroupedExponent S (StageComponent S)
      hfirstProper F q∣stageFamilyResultant S (StageComponent S) F
  exact hp
theorem properStage_activeVFixedPowers:
    ActiveNestedVFixedPowers base hactive hSderiv D
      (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)):=by
  intro q hq hqMonic C₀
  let F:=activeStageVFamily S base hactive hSderiv D
  let W:StageIndexedFactor S (StageComponent S) F:=
    { q:=q,irreducible:=hq,monic:=hqMonic,witness:=C₀}
  have hp:=properStage_indexedFixedFactor_groupedPowerDvd S hfirstProper F W
  change q^stageFamilyGroupedExponent S (StageComponent S)
      hfirstProper F q∣stageFamilyResultant S (StageComponent S) F
  exact hp
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveUVPower6733Research
