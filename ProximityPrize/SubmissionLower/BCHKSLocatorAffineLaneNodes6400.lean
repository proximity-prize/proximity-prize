import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialPairToCode6400

/-! # Base-ring node equation for the polynomial locator affine lane -/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- At a source coordinate, the interpolated affine lane is its defining
bilinear word.  This small wrapper keeps later coefficient maps from
unfolding the full interpolation. -/
theorem score6400PolynomialLocatorPairToCode_eval_coordinate_bilinear
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : IRSProfile.Index) :
    (score6400PolynomialLocatorPairToCode f₀ f₁ q).eval
        (Polynomial.C (IRSProfile.domain i)) =
      (score6400PolynomialLocatorRelationPair q).1.1.eval
            (Polynomial.C (IRSProfile.domain i)) *
          score6400ReceivedPolynomial f₀ f₁ i +
        (score6400PolynomialLocatorRelationPair q).2.1.eval
            (Polynomial.C (IRSProfile.domain i)) *
          score6400FrobeniusReceivedPolynomial f₀ f₁ i := by
  rw [score6400PolynomialLocatorPairToCode_eval_coordinate,
    score6400PolynomialPairRelationWord, polynomialBilinearWord]

end ProximityPrize.SubmissionLower
