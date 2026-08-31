import ProximityPrize.SubmissionLower.ContactProperStageIndexedFamily6733Research
import ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberPrimary6733Research
import ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedFiberSurface6733Research
import ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedGrouped6733Research
import ProximityPrize.SubmissionLower.ContactLocalizedSurfaceNonzero6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6733Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research ContactDelayedTailMultiplicityProvider6732Research
open ContactProperFlagFiberData6733Research ContactProperFlagIndexedFiberData6733Research
open ContactProperFlagIndexedFiberPrimary6733Research
open ContactProperStageIndexedFamily6733Research
open ContactFlagPlaneFiberPrimary6733Research ContactFlagPlaneFiberSurface6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneIndexedFiberSurface6733Research
open ContactFlagPlaneIndexedGrouped6733Research
open ContactLocalizedSurfaceNonzero6733Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagBezout6543Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:Stage K I Gamma x p flag) {A:Type} [Fintype A]
variable (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
theorem stageFamily_surfacePrime:
    (Ideal.span {indexedFiberSurface W.q W.irreducible
      (stageSurfacePlane S F.lam F.mu F.nu F.order)}).IsPrime:=by
  exact indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order
    F.ht S.irreducible_G W.q W.irreducible W.witness
theorem stageFamily_surface_mem
    (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
    stageSurfacePlane S F.lam F.mu F.nu F.order∈
      relationKernel (GenericField K)
        (CoordinateField (GenericField K) (F.component a.1).1) F.order
        (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu)
        (F.ht a.1):=by
  exact indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu
    F.order F.ht a.1
theorem stageFamily_bar_ne
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
    indexedFiberRelationBar F.component F.lam F.mu F.nu F.order F.ht
      W.q W.irreducible (stageSurfacePlane S F.lam F.mu F.nu F.order) a≠⊥:=by
  have hproperLocal:indexedFiberTail W.q W.irreducible
      (stageTailPlane S F.lam F.mu F.nu F.order)∉
      Ideal.span {indexedFiberSurface W.q W.irreducible
        (stageSurfacePlane S F.lam F.mu F.nu F.order)}:=
    indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
      S.irreducible_G hfirstProper W.q W.irreducible W.witness
  exact indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order
    F.ht W.q W.irreducible
    (stageSurfacePlane S F.lam F.mu F.nu F.order)
    (stageTailPlane S F.lam F.mu F.nu F.order)
    (fun b↦indexedStageTail_mem_relation S F.component F.lam F.mu F.nu
      F.order F.ht b.1) hproperLocal a
theorem stageFamily_tail_mem
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
    indexedFiberTail W.q W.irreducible
      (stageTailPlane S F.lam F.mu F.nu F.order)∈
      Ideal.span {indexedFiberSurface W.q W.irreducible
        (stageSurfacePlane S F.lam F.mu F.nu F.order)} ⊔
      indexedFiberRelation F.component F.lam F.mu F.nu F.order F.ht
        W.q W.irreducible a^
        localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
          (F.component a.1):=by
  exact indexedFiberTail_mem_primary S hfirstProper F.component F.lam F.mu
    F.nu F.order F.ht F.finite F.generates W.q W.irreducible a
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6733Research
