import ProximityPrize.SubmissionLower.BCHKSFrobeniusBivariateSpecializationDegree6400
import ProximityPrize.SubmissionLower.BCHKSSealedReceivedFrobeniusDegree6400

/-! # Node values after Frobenius bivariate specialization -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem score6400Frobenius_specializations_eval_domain_eq
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (i : IRSProfile.Index) :
    ((score6400FrobeniusReceivedBivariate f₀ f₁).map
        (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
      ((score6400SealedReceivedInterpolator f₀ f₁ z).map
        koalaSexticFrobenius.toRingHom).eval (IRSProfile.domain i) := by
  have houter := Polynomial.eval_map_apply
    (p := score6400FrobeniusReceivedBivariate f₀ f₁)
    (f := Polynomial.evalRingHom z)
    (Polynomial.C (IRSProfile.domain i))
  have hleft :
      ((score6400FrobeniusReceivedBivariate f₀ f₁).map
          (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        ((score6400FrobeniusReceivedBivariate f₀ f₁).eval
          (Polynomial.C (IRSProfile.domain i))).eval z := by
    simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using houter
  have hnode := congrArg (fun P : IRSProfile.Field[X] ↦ P.eval z)
    (score6400FrobeniusReceivedBivariate_eval_coordinate_wrapped f₀ f₁ i)
  have hright := polynomial_map_eval_of_fixed_locator
    koalaSexticFrobenius
    (score6400SealedReceivedInterpolator f₀ f₁ z)
    (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)
  calc
    ((score6400FrobeniusReceivedBivariate f₀ f₁).map
          (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        ((score6400FrobeniusReceivedBivariate f₀ f₁).eval
          (Polynomial.C (IRSProfile.domain i))).eval z := hleft
    _ = (score6400FrobeniusReceivedNode f₀ f₁ i).eval z := hnode
    _ = koalaSexticFrobenius (f₀ i + z * f₁ i) := by
      rw [score6400FrobeniusReceivedNode_eq,
        score6400FrobeniusReceivedPolynomial_eval]
    _ = koalaSexticFrobenius
          ((score6400SealedReceivedInterpolator f₀ f₁ z).eval
            (IRSProfile.domain i)) := by
      rw [score6400SealedReceivedInterpolator_eval]
    _ = ((score6400SealedReceivedInterpolator f₀ f₁ z).map
          koalaSexticFrobenius.toRingHom).eval
            (IRSProfile.domain i) := hright.symm

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
