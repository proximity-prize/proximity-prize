import ProximityPrize.SubmissionLower.C7
import ProximityPrize.SubmissionLower.Z1
import ProximityPrize.SubmissionLower.S
namespace ProximityPrize.SubmissionLower.RCN102
open RCN011
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
abbrev FiberCoefficient
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):=
 @Localization.AtPrime (Polynomial (RatFunc Omega)) _ (Ideal.span {q})
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
@[reducible] instance fiberLocalizedPlaneSemiring
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Semiring (Polynomial (FiberCoefficient q hq)):=
 Polynomial.commSemiring.toSemiring
def fiberLocalizePlane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   PlaneRing Omega →+*Polynomial (FiberCoefficient q hq):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc Omega)) (FiberCoefficient q hq))
end
end ProximityPrize.SubmissionLower.RCN102
