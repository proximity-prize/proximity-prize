import ProximityPrize.SubmissionLower.Q5

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberPrimary6735Research
open ContactProperDelayedTailCertificate6735Research ContactProperMultiplicitySymbolic6735Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactProperFlagFiberData6733Research
open ContactProperFlagIndexedFiberData6735Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFirstTailCertificate6731Research ContactOriginalFactorLocalDVR6731Research
open ContactGenericInitialPoint ContactTaylorNumerators
open ContactFlagBezout6543Research ContactFlagAffineFamilyDegree6543Research
open ActualCurveCoordinateField ArbitraryPlaneEvaluationFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {A:Type} [Fintype A]
theorem indexedFiberTail_mem_primary
    (S:Stage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
    (component:A → StageComponent S)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (ht:∀ a:A,Transcendental (GenericField K)
      (flagEvaluation (GenericField K) (component a).1 lam mu nu
        (MvPolynomial.X (order 0))))
    (hfinite:∀ a:A,
      letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      FiniteDimensional (RatFunc (GenericField K))
        (CoordinateField (GenericField K) (component a).1))
    (hgen:∀ a:A,
      letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
      IntermediateField.adjoin (RatFunc (GenericField K))
        ({flagEvaluation (GenericField K) (component a).1 lam mu nu
            (MvPolynomial.X (order 2)),
          flagEvaluation (GenericField K) (component a).1 lam mu nu
            (MvPolynomial.X (order 1))}:
          Set (CoordinateField (GenericField K) (component a).1))=⊤)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
    (a:IndexedFactorFiber component lam mu nu order ht q):
    indexedFiberTail q hq (stageTailPlane S lam mu nu order)∈
      Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
        indexedFiberRelation component lam mu nu order ht q hq a^
          localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (component a.1):=by
  let D:=indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
  letI:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=
    D.relationMax
  have hfactor:=D.factor_mem
  have hsurface:=D.surface_mem
  have hcontract:=D.contract
  have htail:=D.tail_eq
  apply proper_global_tail_mem_projected_primary
    (K:=K) (I:=I) (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
    (B:=Polynomial (FiberCoefficient q hq))
    (S:=S) (hfirstProper:=hfirstProper) (C:=component a.1)
    (f:=stageFiberTargetMap S lam mu nu order q hq)
    (surface:=indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order))
    (tail:=indexedFiberTail q hq (stageTailPlane S lam mu nu order))
    (scalar:=stageFiberScalar S lam mu nu order q hq)
    (J:=indexedFiberRelation component lam mu nu order ht q hq a)
  · exact hfactor
  · exact hsurface
  · exact hcontract
  · exact htail
end
end ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberPrimary6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedFamily6735Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactProperFlagFiberData6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedResidueWeight6733Research
open ContactFlagBezout6543Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFlagAffineFamilyDegree6543Research
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:Stage K I Gamma x p flag) (A:Type) [Fintype A]
structure StageIndexedFlagFamily where
  component:A → StageComponent S
  injective:Function.Injective component
  lam:GenericField K
  mu:GenericField K
  nu:GenericField K
  order:Fin 3 ≃ Fin 3
  ht:∀ a,Transcendental (GenericField K)
    (flagEvaluation (GenericField K) (component a).1 lam mu nu
      (MvPolynomial.X (order 0)))
  finite:∀ a,
    letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
    FiniteDimensional (RatFunc (GenericField K))
      (CoordinateField (GenericField K) (component a).1)
  generates:∀ a,
    letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
    IntermediateField.adjoin (RatFunc (GenericField K))
      ({flagEvaluation (GenericField K) (component a).1 lam mu nu
          (MvPolynomial.X (order 2)),
        flagEvaluation (GenericField K) (component a).1 lam mu nu
          (MvPolynomial.X (order 1))}:
        Set (CoordinateField (GenericField K) (component a).1))=⊤
  positive:0 < (stageSurfacePlane S lam mu nu order).natDegree
structure StageIndexedFactor (F:StageIndexedFlagFamily S A) where
  q:Polynomial (RatFunc (GenericField K))
  irreducible:Irreducible q
  monic:q.Monic
  witness:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def stageFamilyGroupedExponent
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
    (F:StageIndexedFlagFamily S A)
    (q:Polynomial (RatFunc (GenericField K))):ℕ:=
  ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
    localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
      indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
        F.ht F.finite a.1
noncomputable def stageFamilyResultant (F:StageIndexedFlagFamily S A):
    Polynomial (RatFunc (GenericField K)):=
  Polynomial.resultant (stageSurfacePlane S F.lam F.mu F.nu F.order)
    (stageTailPlane S F.lam F.mu F.nu F.order)
    (stageSurfacePlane S F.lam F.mu F.nu F.order).natDegree
    (stageTailPlane S F.lam F.mu F.nu F.order).natDegree
@[simp] theorem stageFamilyGroupedExponent_eq
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))
    (F:StageIndexedFlagFamily S A) (q):
    stageFamilyGroupedExponent S A hfirstProper F q=
      ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
        localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
          indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
            F.ht F.finite a.1:=rfl
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedFamily6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6735Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperCutSeedCount ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperStageActiveFamilies6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6735Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research ContactDelayedTailMultiplicityProvider6732Research
open ContactProperFlagFiberData6733Research ContactProperFlagIndexedFiberData6735Research
open ContactProperFlagIndexedFiberPrimary6735Research
open ContactProperStageIndexedFamily6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
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
      (ContactTwoTailParameters6735Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6735Research
end
