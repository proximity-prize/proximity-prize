import ProximityPrize.SubmissionLower.ContactFlagInterpolation

namespace ProximityPrize.SubmissionLower.ContactStackedParameters

open ContactInterpolation
open ContactFlagInterpolation ContactFlagRankKernel
open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem coefficientCount_eq_sum_range_of_weighted_cutoff
    (D w L s t : ℕ) (ht : t ≤ L + 1) (hD : D ≤ w * t) :
    coefficientCount D w L s =
      ∑ i ∈ Finset.range t,
        ∑ j ∈ Finset.range (s + 1),
          (L + 1 - i - j) * (D - w * i - (w - 1) * j) := by
  have hsplit : L + 1 = t + (L + 1 - t) := by omega
  unfold coefficientCount
  rw [hsplit, Finset.sum_range_add]
  have htail :
      (∑ x ∈ Finset.range (L + 1 - t),
        ∑ j ∈ Finset.range (s + 1),
          (t + (L + 1 - t) - (t + x) - j) *
            (D - w * (t + x) - (w - 1) * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hti : t ≤ t + i := by omega
    have hzero : D - w * (t + i) = 0 :=
      Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
    simp [hzero]
  rw [htail, add_zero]

end ProximityPrize.SubmissionLower.ContactStackedParameters
