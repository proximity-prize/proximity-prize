import ProximityPrize.SubmissionLower.ContactFlagPlaneFiberBase6733Research
import ProximityPrize.SubmissionLower.ContactFlagPlaneSurfaceLocalAdapter6732Research
import ProximityPrize.SubmissionLower.ContactProperMultiplicitySymbolic6732Research
namespace ProximityPrize.SubmissionLower.ContactProperFlagFiberData6733Research
open ContactProperDelayedTailCertificate6732Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFlagBezout6543Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFirstTailCertificate6731Research
open ContactTaylorNumerators
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ContactFlagTriangularProjectionResearch
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
abbrev StageComponent (S:Stage K I Gamma x p flag):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
    PlaneRing (GenericField K):=
  flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
    PlaneRing (GenericField K):=
  flagPlaneMap (GenericField K) lam mu nu order
    (globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
    MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
  ((fiberLocalizePlane q hq).comp
    (flagPlaneMap (GenericField K) lam mu nu order)).comp
      (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag)
    (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
    Polynomial (FiberCoefficient q hq):=
  fiberLocalizePlane q hq
    (flagPlaneMap (GenericField K) lam mu nu order
      (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
        (ContactTwoTailParameters6733Research.w+1))))
end
end ProximityPrize.SubmissionLower.ContactProperFlagFiberData6733Research
