import ProximityPrize.SubmissionLower.BCHKSReceivedBivariateNodes6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- A small ring-generic wrapper for the evaluation calculation.  Keeping
the calculation generic prevents elaboration from reducing the concrete
full-domain interpolators. -/
theorem polynomial_residual_eval_eq_zero
    {R : Type} [CommRing R]
    (A B C W V : R[X]) (x w v : R)
    (hW : W.eval x = w) (hV : V.eval x = v)
    (hrelation : C.eval x = A.eval x * w + B.eval x * v) :
    (A * W + B * V - C).eval x = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul, hW, hV, hrelation,
    sub_self]

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
