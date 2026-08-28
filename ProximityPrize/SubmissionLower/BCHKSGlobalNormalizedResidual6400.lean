import ProximityPrize.SubmissionLower.BCHKSGlobalNormalizedResidualDef6400

/-!
# The global normalized received residual

This module isolates the coordinate identity used by the owner-independent
key equation.  Compiling it separately keeps the full-domain interpolation
definitions opaque when the nodal divisor is selected downstream.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSPrimitiveTripleRelation6400

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- The normalized received residual vanishes identically in the challenge
at every coordinate outside the fixed primitive-factor container. -/
theorem score6400GlobalNormalizedResidual_eval_coordinate
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
    (A * score6400ReceivedBivariate f₀ f₁ +
        B * score6400FrobeniusReceivedBivariate f₀ f₁ - C).eval
      (Polynomial.C (IRSProfile.domain i)) = 0 := by
  have hrelation :
      C.eval (Polynomial.C (IRSProfile.domain i)) =
        A.eval (Polynomial.C (IRSProfile.domain i)) *
            score6400ReceivedNode f₀ f₁ i +
          B.eval (Polynomial.C (IRSProfile.domain i)) *
            score6400FrobeniusReceivedNode f₀ f₁ i := by
    rw [score6400ReceivedNode_eq, score6400FrobeniusReceivedNode_eq]
    exact quotient_relationWord_at_coordinate
      f₀ f₁ q H A B C hAfactor hBfactor hCfactor i hi
  have hreceived :
      (score6400ReceivedBivariate f₀ f₁).eval
          (Polynomial.C (IRSProfile.domain i)) =
        score6400ReceivedNode f₀ f₁ i :=
    score6400ReceivedBivariate_eval_coordinate_wrapped f₀ f₁ i
  have hfrobenius :
      (score6400FrobeniusReceivedBivariate f₀ f₁).eval
          (Polynomial.C (IRSProfile.domain i)) =
        score6400FrobeniusReceivedNode f₀ f₁ i :=
    score6400FrobeniusReceivedBivariate_eval_coordinate_wrapped f₀ f₁ i
  exact polynomial_residual_eval_eq_zero (R := IRSProfile.Field[X]) A B C
    (score6400ReceivedBivariate f₀ f₁)
    (score6400FrobeniusReceivedBivariate f₀ f₁)
    (Polynomial.C (IRSProfile.domain i))
    (score6400ReceivedNode f₀ f₁ i)
    (score6400FrobeniusReceivedNode f₀ f₁ i)
    hreceived hfrobenius hrelation

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
