import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem ambient_rank : localRankBound 89 109000 27 = 9308370120 := by decide
theorem ambient_nullity :
    coefficientCount 16184205 131071 109000 27 -
      262144 * localRankBound 89 109000 27 = 13032173188195 := by
  rw [ambient_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    16184205 131071 109000 27 124 (by decide) (by decide)]
  decide

theorem A77_rank : localRankBound 77 109000 23 = 6008880792 := by decide
theorem A77_nullity :
    coefficientCount 14002065 131071 109000 23 -
      262144 * localRankBound 77 109000 23 = 6753289983658 := by
  rw [A77_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    14002065 131071 109000 23 107 (by decide) (by decide)]
  decide

theorem A77_fixed_rank : localRankBound 77 2567 23 = 139739440 := by decide
theorem A77_fixed_nullity :
    coefficientCount 14002065 131071 2567 23 -
      262144 * localRankBound 77 2567 23 = 38456280382 := by
  rw [A77_fixed_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    14002065 131071 2567 23 107 (by decide) (by decide)]
  decide
theorem A77_fixed_shape : 14002065 + 23 ≤ 131071 * (106 + 1) := by decide
theorem A77_fixed_capacity :
    14002065 - 50775 ≤ (77 - 1) * 181845 + (131071 - 1) := by decide

theorem Y_rank : localRankBound 50 100000 15 = 1563672240 := by decide
theorem Y_nullity :
    coefficientCount 9092250 131071 100000 15 -
      262144 * localRankBound 50 100000 15 = 92028762220 := by
  rw [Y_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9092250 131071 100000 15 70 (by decide) (by decide)]
  decide

theorem Y_ys67_quotient_lt (r : ℕ) (hr : r ≤ 15) :
    coefficientCount (9092250 - (67 * 131071 - r)) 131071
      (100000 - 67) (15 - r) <
    coefficientCount 9092250 131071 100000 15 -
      262144 * localRankBound 50 100000 15 := by
  rw [Y_nullity]
  interval_cases r <;>
    rw [coefficientCount_eq_sum_range_of_weighted_cutoff
      _ 131071 99933 _ 4 (by decide) (by decide)] <;> decide

theorem R_rank : localRankBound 50 100000 14 = 1488694080 := by decide
theorem R_nullity :
    coefficientCount 9092250 131071 100000 14 -
      262144 * localRankBound 50 100000 14 = 23319716365 := by
  rw [R_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9092250 131071 100000 14 70 (by decide) (by decide)]
  decide

theorem B_rank : localRankBound 97 1799 30 = 196219894 := by decide
theorem B_nullity :
    coefficientCount 17638965 131071 1799 30 -
      262144 * localRankBound 97 1799 30 = 223918084 := by
  rw [B_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17638965 131071 1799 30 135 (by decide) (by decide)]
  decide

theorem B_total_quotient_lt :
    coefficientCount 17638965 131071 2 30 <
    coefficientCount 17638965 131071 1799 30 -
      262144 * localRankBound 97 1799 30 := by
  rw [B_nullity]
  decide

end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
