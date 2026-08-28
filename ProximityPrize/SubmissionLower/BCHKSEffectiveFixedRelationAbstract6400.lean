import ProximityPrize.SubmissionLower.BCHKSMappedBilinearNode6400

/-! # Algebra for restoring a relation at quotient-zero nodes -/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- At a node where the common quotient vanishes, its global factorization
forces the normalized affine received relation, even if that node belonged
to the original fixed defect. -/
theorem bilinear_relation_of_factorization_at_quotient_root
    {R : Type} [CommRing R]
    (L K A B C W V : R[X]) (x w v : R)
    (hglobal : L * K = A * W + B * V - C)
    (hW : W.eval x = w) (hV : V.eval x = v)
    (hK : K.eval x = 0) :
    C.eval x = A.eval x * w + B.eval x * v := by
  have hglobalEval := congrArg (fun P : R[X] ↦ P.eval x) hglobal
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_mul, hW, hV, hK, mul_zero]
    at hglobalEval
  exact (sub_eq_zero.mp hglobalEval.symm).symm

/-- Scaling both homogeneous coefficients scales the whole error relation. -/
theorem scaled_bilinear_error_eq_zero
    {R : Type} [CommRing R]
    (r a b e f : R) (h : a * e + b * f = 0) :
    (r * a) * e + (r * b) * f = 0 := by
  calc
    (r * a) * e + (r * b) * f = r * (a * e + b * f) := by ring
    _ = 0 := by rw [h, mul_zero]

end ProximityPrize.SubmissionLower
