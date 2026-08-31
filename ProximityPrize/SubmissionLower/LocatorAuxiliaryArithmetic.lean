import ProximityPrize.SubmissionLower.LocatorArithmetic

/- One fixed A74 kernel suffices for every replacement cell. -/
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem auxiliary_rank : localRankBound 74 2773 22 = 134051774 := by decide

theorem auxiliary_nullity :
    coefficientCount 13456530 131071 2773 22 -
      262144 * localRankBound 74 2773 22 = 38932026630 := by
  rw [auxiliary_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13456530 131071 2773 22 103 (by decide) (by decide)]
  decide

theorem auxiliary_shape : 13456530 + 22 ≤ 131071 * (102 + 1) := by decide
theorem auxiliary_capacity :
    13456530 - 50775 ≤ (74 - 1) * 181845 + (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
