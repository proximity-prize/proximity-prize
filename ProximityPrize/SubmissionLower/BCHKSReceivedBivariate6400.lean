import ProximityPrize.SubmissionLower.BCHKSErrorEvaluatorSemilinear6400

/-!
# Received affine interpolation with the challenge retained

This file isolates the two full-domain interpolators used by the common
inhomogeneous key equation.  Keeping it as a small compiled dependency avoids
re-elaborating the production interpolation machinery in downstream proofs.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSErrorEvaluatorSemilinear6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

universe u

/-- A generic opacity barrier.  Its defining equation is proved once at an
abstract type, so using it does not package concrete interpolation terms into
the irreducibility witness. -/
irreducible_def bchksInterpolationSeal {R : Type u} (x : R) : R := x

/-- An irreducible name for one received challenge polynomial.  The wrapper
prevents downstream conversion from unfolding the concrete affine term. -/
noncomputable def score6400ReceivedNode
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) : IRSProfile.Field[X] :=
  bchksInterpolationSeal (score6400ReceivedPolynomial f₀ f₁ i)

/-- An irreducible name for one coefficient-Frobenius received polynomial.
In particular, downstream conversion cannot expand its formal `Z^p` term. -/
noncomputable def score6400FrobeniusReceivedNode
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (i : IRSProfile.Index) : IRSProfile.Field[X] :=
  bchksInterpolationSeal
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i)

/-- The received affine interpolator with the challenge retained as the
coefficient variable. -/
noncomputable def score6400ReceivedBivariate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    IRSProfile.Field[X][X] :=
  bchksInterpolationSeal <|
    algebraLagrangeInterpolate Finset.univ
      (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
      (score6400ReceivedNode f₀ f₁)

/-- The coefficient-Frobenius received interpolator, still expressed using
only the sparse challenge lanes `1,Z^p`. -/
noncomputable def score6400FrobeniusReceivedBivariate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) :
    IRSProfile.Field[X][X] :=
  bchksInterpolationSeal <|
    algebraLagrangeInterpolate Finset.univ
      (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
      (score6400FrobeniusReceivedNode f₀ f₁)

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
