import ProximityPrize.SubmissionLower.ContactProperStageIndexedFamily6733Research
import ProximityPrize.SubmissionLower.ContactActiveNestedFlagData6733Research
import ProximityPrize.SubmissionLower.ContactFlagProjectionPositivity6543Research
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6733Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperCutSeedCount ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6733Research
open ContactActiveNestedFlagData6733Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactWeakSeparableSeparatorResearch
open ContactFlagProjectionPositivity6543Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagTriangularProjectionResearch
open ContactFlagBezout6543Research
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
abbrev ActiveStageZIndex (S:Stage K I Gamma x p flag):=
  ActiveNestedZIndex (G:=S.G)
    (T:=globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (H:=regularitySurface (polynomialEmbedding K) S.F)
variable (S:Stage K I Gamma x p flag)
variable (base:∀ C:StageComponent S,SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:StageComponent S,
  KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
      (coordinate (GenericField K) C.1 0)≠0∨
    KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
      (coordinate (GenericField K) C.1 2)≠0)
variable (hZ:∀ C:StageComponent S,LiteralProjectionGate C 2)
variable (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G≠0)
variable (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
noncomputable def activeStageZFamily:
    StageIndexedFlagFamily S (ActiveStageZIndex S) where
  component:=activeNestedZComponent
  injective:=activeNestedZComponent_injective
  lam:=D.lam
  mu:=D.mu
  nu:=D.mu*D.lam
  order:=zOrder
  ht:=activeNestedZTranscendental base hactive hSderiv D
  finite:=activeNestedZFinite base hactive hZ hSderiv D
  generates:=activeNestedZGenerates base hactive hSderiv D
  positive:=(flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
noncomputable def activeStageUFamily:StageIndexedFlagFamily S (StageComponent S) where
  component:=fun C↦C
  injective:=Function.injective_id
  lam:=D.lam
  mu:=D.mu
  nu:=D.mu*D.lam
  order:=uOrder
  ht:=activeNestedUTranscendental base hactive hSderiv D
  finite:=activeNestedUFinite base hactive hSderiv D
  generates:=activeNestedUGenerates base hactive hSderiv D
  positive:=(flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
noncomputable def activeStageVFamily:StageIndexedFlagFamily S (StageComponent S) where
  component:=fun C↦C
  injective:=Function.injective_id
  lam:=D.lam
  mu:=D.mu
  nu:=D.mu*D.lam
  order:=vOrder
  ht:=activeNestedVTranscendental base hactive hSderiv D
  finite:=activeNestedVFinite base hactive hSderiv D
  generates:=activeNestedVGenerates base hactive hSderiv D
  positive:=flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional
end
end ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6733Research
