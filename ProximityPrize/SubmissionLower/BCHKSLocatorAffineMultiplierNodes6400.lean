import ProximityPrize.SubmissionLower.BCHKSChallengeFractionMap6400

/-! # Fraction-field node identities for locator affine lanes -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The mapped affine lane has its defining bilinear value at every source
coordinate.  This packages the concrete interpolation expression behind a
small node interface. -/
theorem score6400_affineLane_fraction_eval_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (i : IRSProfile.Index) :
    ((score6400PolynomialLocatorPairToCode f₀ f₁ q).map
          score6400ChallengeIota).eval
        (score6400ChallengeFractionDomain i) =
      ((score6400PolynomialLocatorRelationPair q).1.1.map
          score6400ChallengeIota).eval
            (score6400ChallengeFractionDomain i) *
          score6400ChallengeIota
            (score6400ReceivedPolynomial f₀ f₁ i) +
        ((score6400PolynomialLocatorRelationPair q).2.1.map
          score6400ChallengeIota).eval
            (score6400ChallengeFractionDomain i) *
          score6400ChallengeIota
            (score6400FrobeniusReceivedPolynomial f₀ f₁ i) := by
  rw [score6400ChallengeFractionDomain_apply]
  exact score6400ChallengeIota_bilinear_eval
    (score6400PolynomialLocatorPairToCode f₀ f₁ q)
    (score6400PolynomialLocatorRelationPair q).1.1
    (score6400PolynomialLocatorRelationPair q).2.1
    (Polynomial.C (IRSProfile.domain i))
    (score6400ReceivedPolynomial f₀ f₁ i)
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i)
    (score6400PolynomialLocatorPairToCode_eval_coordinate_bilinear f₀ f₁ q i)

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower
