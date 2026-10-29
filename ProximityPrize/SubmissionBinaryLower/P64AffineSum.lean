import ProximityPrize.SubmissionBinaryLower.P64Algebra

namespace ProximityPrize.SubmissionBinaryLower.P64Interp

/-- Closed form of a sum of products of two affine functions of the index. -/
theorem six_mul_sum_range (a b c d : ℤ) (N : ℕ) :
    6 * ∑ j ∈ Finset.range N, (a - b * j) * (c - d * j) =
      6 * a * c * N - 3 * (a * d + b * c) * N * (N - 1) + b * d * (N - 1) * N * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

end ProximityPrize.SubmissionBinaryLower.P64Interp
