import ProximityPrize.SubmissionLower.BCHKSCyclicNormErrorEvaluator6400

/-! # Multiplicativity of the score-64 cyclic norm -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSCyclicNormErrorEvaluator6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem koalaFrobeniusConjugate_mul
    (P Q : IRSProfile.Field[X]) (n : Nat) :
    koalaFrobeniusConjugate n (P * Q) =
      koalaFrobeniusConjugate n P * koalaFrobeniusConjugate n Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, koalaFrobeniusConjugate,
        koalaFrobeniusConjugate, ih, Polynomial.map_mul]

theorem koalaCyclicNormSix_mul
    (P Q : IRSProfile.Field[X]) :
    koalaCyclicNormSix (P * Q) =
      koalaCyclicNormSix P * koalaCyclicNormSix Q := by
  simp only [koalaCyclicNormSix, koalaFrobeniusConjugate_mul]
  ring

/-- Cancel a common nonzero polynomial factor from equality of cyclic norms. -/
theorem koalaCyclicNormSix_cancel_left
    (R A B : IRSProfile.Field[X]) (hR : R ≠ 0)
    (h : koalaCyclicNormSix (R * A) =
      koalaCyclicNormSix (R * B)) :
    koalaCyclicNormSix A = koalaCyclicNormSix B := by
  rw [koalaCyclicNormSix_mul, koalaCyclicNormSix_mul] at h
  exact mul_left_cancel₀ (koalaCyclicNormSix_ne_zero R hR) h

end BCHKSCyclicNormErrorEvaluator6400
end ProximityPrize.SubmissionLower
