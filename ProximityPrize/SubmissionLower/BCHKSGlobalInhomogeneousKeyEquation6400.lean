import ProximityPrize.SubmissionLower.BCHKSGlobalNormalizedResidual6400
import ProximityPrize.SubmissionLower.BCHKSMappedNodalCofactor6400

/-!
# A common inhomogeneous key equation for the rank-one branch

The normalized primitive triple represents the received affine word away
from one fixed coordinate container.  Interpolating the received word while
retaining the challenge variable therefore produces a *single* bivariate
residual.  The locator of every coordinate outside the fixed container
divides that residual over the challenge polynomial ring.

The quotient is independent of the decoded owner.  After specialization,
every owner error evaluator consequently satisfies the exact equation

`E * K = L_Fixed * (A * D + B * sigma(D))`,

where `E` is the full actual-error locator.  This strengthens the earlier
per-owner divisibility statement: all owner dependence is confined to
`E,D`, while `K` is chosen once from the received pair and primitive triple.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSPrimitiveTripleRelation6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- One owner-independent quotient controls every retained challenge and
decoded owner attached to the same primitive triple. -/
theorem exists_score6400_globalNormalizedResidualQuotient
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C : IRSProfile.Field[X][X])
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C) :
    ∃ K : IRSProfile.Field[X][X],
      (outsideAgreementLocator IRSProfile.domain Finset.univ
          (fixedCoordinateDefect H)).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C := by
  have hdvd := mapped_outsideAgreementLocator_dvd
    IRSProfile.domain Finset.univ (fixedCoordinateDefect H)
    (A * score6400ReceivedBivariate f₀ f₁ +
      B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (fun i _hi hiFixed ↦
      score6400GlobalNormalizedResidual_eval_coordinate
        f₀ f₁ q H A B C hAfactor hBfactor hCfactor i hiFixed)
  obtain ⟨K, hK⟩ := hdvd
  exact ⟨K, hK.symm⟩

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
