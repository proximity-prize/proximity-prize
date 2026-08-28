import ProximityPrize.SubmissionLower.BCHKSEffectiveFixedRelationAbstract6400
import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialPairToCode6400

/-! # Specialized challenge-polynomial factorization node -/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- Opaque specialization of the quotient-root bilinear calculation to the
production challenge polynomial ring. -/
theorem score6400ChallengePolynomial_bilinear_relation_of_factorization
    (L K A B C W V : IRSProfile.Field[X][X])
    (x w v : IRSProfile.Field[X])
    (hglobal : L * K = A * W + B * V - C)
    (hW : W.eval x = w) (hV : V.eval x = v)
    (hK : K.eval x = 0) :
    C.eval x = A.eval x * w + B.eval x * v := by
  exact bilinear_relation_of_factorization_at_quotient_root
    L K A B C W V x w v hglobal hW hV hK

end ProximityPrize.SubmissionLower
