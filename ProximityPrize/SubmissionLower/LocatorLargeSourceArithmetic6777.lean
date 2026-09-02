import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorLargeSourceArithmetic6777

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- The role-separated long C241 kernel used only by the local helper-factor
    switch.  It is not the residual or common-GCD ambient source. -/
def helperLength : ℕ := 457347
def helperWeighted : ℕ := 43769938
def helperSlope : ℕ := 71
def helperMultiplicity : ℕ := 241
def helperY : ℕ := 333

theorem helper_rank_exact :
    localRankBound helperMultiplicity helperLength helperSlope =
      734070413760 := by decide

theorem helper_coefficient_exact :
    coefficientCount helperWeighted 131071 helperLength helperSlope =
      193728546769719642 := by
  change coefficientCount 43769938 131071 457347 71 =
    193728546769719642
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    43769938 131071 457347 71 334 (by decide) (by decide)]
  decide

theorem helper_nullity_exact :
    coefficientCount helperWeighted 131071 helperLength helperSlope -
      262144 * localRankBound helperMultiplicity helperLength helperSlope =
        1296392225018202 := by
  rw [helper_coefficient_exact, helper_rank_exact]

theorem helper_shape :
    helperWeighted + helperSlope ≤ 131071 * (helperY + 1) := by decide

theorem helper_capacity :
    helperWeighted - 50548 ≤
      (helperMultiplicity - 1) * 181618 + (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorLargeSourceArithmetic6777
