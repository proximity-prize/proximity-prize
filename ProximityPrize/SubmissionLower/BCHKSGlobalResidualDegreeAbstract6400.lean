import ProximityPrize.SubmissionLower.BCHKSCommonLocatorKeyEquation6400

/-! # Abstract outer-degree bound for an inhomogeneous residual -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem inhomogeneous_residual_natDegree_lt
    {R : Type} [Ring R]
    (A B C W V : R[X]) (n d : Nat)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hW : W.natDegree < n) (hV : V.natDegree < n)
    (hC : C.natDegree < n + d) :
    (A * W + B * V - C).natDegree < n + d := by
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  apply max_lt
  · apply (Polynomial.natDegree_add_le _ _).trans_lt
    apply max_lt
    · exact Polynomial.natDegree_mul_le.trans_lt (by omega)
    · exact Polynomial.natDegree_mul_le.trans_lt (by omega)
  · exact hC

/-- A nonzero left factor cannot make the right factor's degree exceed the
degree of the product. -/
theorem right_factor_natDegree_le
    {R : Type} [Semiring R] [NoZeroDivisors R]
    (P H Q : R[X]) (hH : H ≠ 0) (hfactor : P = H * Q) :
    Q.natDegree ≤ P.natDegree := by
  by_cases hQ : Q = 0
  · rw [hQ, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · have hdegree := congrArg Polynomial.natDegree hfactor
    rw [Polynomial.natDegree_mul hH hQ] at hdegree
    omega

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
