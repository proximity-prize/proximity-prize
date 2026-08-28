import ProximityPrize.SubmissionLower.BCHKSLocatorAffineMultiplierNodes6400
import ProximityPrize.SubmissionLower.BCHKSGlobalNormalizedResidual6400

/-! # Fraction-field node identity for the normalized locator affine lane -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSPrimitiveTripleRelation6400

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The normalized primitive affine lane has the corresponding mapped node
value outside its fixed coordinate defect. -/
theorem score6400_normalizedAffineLane_fraction_eval_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C : IRSProfile.Field[X][X])
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C)
    (i : IRSProfile.Index) (hi : i ∉ fixedCoordinateDefect H) :
    (C.map score6400ChallengeIota).eval
        (score6400ChallengeFractionDomain i) =
      (A.map score6400ChallengeIota).eval
            (score6400ChallengeFractionDomain i) *
          score6400ChallengeIota
            (score6400ReceivedPolynomial f₀ f₁ i) +
        (B.map score6400ChallengeIota).eval
            (score6400ChallengeFractionDomain i) *
          score6400ChallengeIota
            (score6400FrobeniusReceivedPolynomial f₀ f₁ i) := by
  rw [score6400ChallengeFractionDomain_apply]
  exact score6400ChallengeIota_bilinear_eval C A B
    (Polynomial.C (IRSProfile.domain i))
    (score6400ReceivedPolynomial f₀ f₁ i)
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i)
    (quotient_relationWord_at_coordinate
      f₀ f₁ q H A B C hAfactor hBfactor hCfactor i hi)

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower
