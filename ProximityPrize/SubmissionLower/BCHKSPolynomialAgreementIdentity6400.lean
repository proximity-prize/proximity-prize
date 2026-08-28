import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial identity from bounded degree and indexed agreement

This small wrapper keeps concrete code parameters out of the interpolation
uniqueness argument.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false

variable {K ι : Type} [Field K]

theorem polynomial_eq_of_natDegree_lt_card_of_eval_index_eq
    (C R : K[X]) (A : Finset ι) (v : ι → K)
    (hv : Set.InjOn v A)
    (hC : C.natDegree < A.card)
    (hR : R.natDegree < A.card)
    (heval : ∀ i ∈ A, C.eval (v i) = R.eval (v i)) :
    C = R := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := A) (v := v) hv
  · by_cases hzero : C = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact WithBot.coe_lt_coe.mpr hC
  · by_cases hzero : R = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      exact WithBot.coe_lt_coe.mpr hR
  · exact heval

end ProximityPrize.SubmissionLower
