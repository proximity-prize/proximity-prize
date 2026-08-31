import ProximityPrize.SubmissionLower.ContactProperStageIndexedSpecialization6733Research
import ProximityPrize.SubmissionLower.ContactProperStageIndexedFixedFactor6733Research
import ProximityPrize.SubmissionLower.ContactLocalizedSurfaceNonzero6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedPbar6733Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactDelayedTailMultiplicityProvider6732Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperStageIndexedFamily6733Research
open ContactProperFlagFiberData6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneIndexedFiberSurface6733Research
open ContactFlagPlaneFiberSurface6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactLocalizedSurfaceNonzero6733Research
open ContactProperStageIndexedSpecialization6733Research
open ContactProperStageIndexedFixedFactor6733Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagBezout6543Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:Stage K I Gamma x p flag) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    StageFamilySurfaceModNonzero S F W:=by
  rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
  let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
  have hspecial:=stageFamily_surface_specialization_ne S F q hq
    (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
  change surface.map (AdjoinRoot.mk q)≠0 at hspecial
  change (indexedFiberSurface q hq surface).map
    (IsLocalRing.residue (FiberCoefficient q hq))≠0
  subst q
  exact localized_surface_residue_ne_zero (GenericField K)
    (CoordinateField (GenericField K) (F.component a).1) F.order
    (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
    (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedPbar6733Research
