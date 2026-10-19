import ProximityPrize.SubmissionBinaryLower.BCHKSLinearSelectedCore
import ProximityPrize.SubmissionBinaryLower.BCHKSFactorPigeon
import ProximityPrize.SubmissionBinaryLower.BCHKSDoubleCounting

namespace ProximityPrize.SubmissionBinaryLower

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Put `Z=z` and `X=x` in a polynomial in `F[Z][X][Y]`, leaving `Y`. -/
noncomputable def linearHSpecialization {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (z x : F) : F[X] :=
  R.map ((Polynomial.evalRingHom x).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)))

/-- Put `X=x` and the symbolic affine value `Y=U₀(x)+Z U₁(x)` in `R`.
The result is a polynomial in `Z`. -/
noncomputable def linearQSpecialization {F : Type*} [Field F]
    (R : Polynomial (Polynomial (Polynomial F))) (U₀ U₁ : F → F) (x : F) : F[X] :=
  Polynomial.eval (Polynomial.C (U₀ x) + Polynomial.X * Polynomial.C (U₁ x))
    (triSpecializeX R x)

end ProximityPrize.SubmissionBinaryLower
