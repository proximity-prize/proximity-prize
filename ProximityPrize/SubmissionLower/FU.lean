import ProximityPrize.SubmissionLower.N
import ProximityPrize.SubmissionLower.FX
namespace ProximityPrize.SubmissionLower.RCN245
open RCN244
open RCN135 RCN136
open RCN074
open RCN095
open RCN102
open RCN113
open RCN120
open RCN086
open RCN313
open RCN002 RCN011
open RCN125
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
abbrev StageComponent (S:Stage K I Gamma x p flag errorCap stageSupport):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
 ((fiberLocalizePlane q hq).comp
   (flagPlaneMap (GenericField K) lam mu nu order)).comp
     (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq
   (flagPlaneMap (GenericField K) lam mu nu order
     (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
       (RCN326.w+1))))
end
end ProximityPrize.SubmissionLower.RCN245
