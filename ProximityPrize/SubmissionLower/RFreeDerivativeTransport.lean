import ProximityPrize.SubmissionLower.RFreeDerivativeCertificate

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveZPower6735Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperCutSeedCount ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6735Research
open ContactProperStageIndexedPower6735Research
open ContactProperStageActiveFamilies6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperStageActiveZPower6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveUVPower6735Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperCutSeedCount ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6735Research
open ContactProperStageIndexedPower6735Research
open ContactProperStageActiveFamilies6735Research
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
  (ContactTwoTailParameters6735Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperStageActiveUVPower6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveFixedPowers6735Research
open ProximityPrize.Benchmark
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperStageActiveProvider6735Research
open ContactTwoTailParameters6735Research
open ContactTerminalAdaptiveProjection6656Research
open ContactProperStageActiveZPower6735Research
open ContactProperStageActiveUVPower6735Research
open ContactActiveNestedFixedPowers6733Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactWeakSeparableSeparatorResearch
open ContactFlagBezout6543Research
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
theorem activeStageFixedPowerProvider6733:ActiveStageFixedPowerProvider6733:=by
  intro Gamma flag S hfirstProper base hactive hZ D
  let hSderiv:=residualStage_pderiv_one_ne_zero_of_support S
  exact {
    z:=properStage_activeZFixedPowers S hfirstProper base hactive hZ hSderiv D
    u:=properStage_activeUFixedPowers S hfirstProper base hactive hSderiv D
    v:=properStage_activeVFixedPowers S hfirstProper base hactive hSderiv D}
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveFixedPowers6735Research
end
