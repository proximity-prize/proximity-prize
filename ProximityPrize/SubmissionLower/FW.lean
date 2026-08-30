import ProximityPrize.SubmissionLower.FV
namespace ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberPrimary6733Research
open ContactProperDelayedTailCertificate6732Research ContactProperMultiplicitySymbolic6732Research
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactProperFlagFiberData6733Research
open ContactProperFlagIndexedFiberData6733Research
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
     (ContactTwoTailParameters6733Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperFlagIndexedFiberPrimary6733Research
