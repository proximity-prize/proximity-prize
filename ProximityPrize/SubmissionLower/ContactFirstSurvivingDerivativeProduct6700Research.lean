import ProximityPrize.Benchmark.TargetLower

import ProximityPrize.SubmissionLower.DifferentialTaylorCoefficients

 















namespace ProximityPrize.SubmissionLower
namespace ContactFirstSurvivingDerivativeProduct6700Research

open Finset
open DifferentialTaylorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K A L : Type*}
  [CommRing K] [CommRing A] [Algebra K A] [CommRing L]

 

theorem map_iterate_product_at_first_survival
    (D : Derivation K A A) (value : A →+* L)
    (a b : A) (r s : ℕ)
    (ha : ∀ i < r, value (D^[i] a) = 0)
    (hb : ∀ j < s, value (D^[j] b) = 0) :
    value (D^[r + s] (a * b)) =
      (r + s).choose r • (value (D^[r] a) * value (D^[s] b)) := by
  rw [iterate_product, map_sum]
  simp_rw [map_nsmul, map_mul]
  apply Finset.sum_eq_single (r, s)
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = r + s := mem_antidiagonal.mp hij
    rcases lt_trichotomy ij.1 r with hir | hir | hir
    · rw [ha ij.1 hir, zero_mul, nsmul_zero]
    · have hjs : ij.2 = s := by omega
      exact (hne (Prod.ext hir hjs)).elim
    · have hjs : ij.2 < s := by omega
      rw [hb ij.2 hjs, mul_zero, nsmul_zero]
  · simp

 



theorem map_iterate_product_ne_zero_at_first_survival
    [NoZeroDivisors L]
    (D : Derivation K A A) (value : A →+* L)
    (a b : A) (r s : ℕ)
    (ha : ∀ i < r, value (D^[i] a) = 0)
    (hb : ∀ j < s, value (D^[j] b) = 0)
    (hchoose : ((r + s).choose r : L) ≠ 0)
    (har : value (D^[r] a) ≠ 0)
    (hbs : value (D^[s] b) ≠ 0) :
    value (D^[r + s] (a * b)) ≠ 0 := by
  rw [map_iterate_product_at_first_survival D value a b r s ha hb,
    nsmul_eq_mul]
  exact mul_ne_zero hchoose (mul_ne_zero har hbs)

end ContactFirstSurvivingDerivativeProduct6700Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFirstSurvivingDerivativeProduct6700Research.map_iterate_product_at_first_survival
#print axioms ProximityPrize.SubmissionLower.ContactFirstSurvivingDerivativeProduct6700Research.map_iterate_product_ne_zero_at_first_survival
