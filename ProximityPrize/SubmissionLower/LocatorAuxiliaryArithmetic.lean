import ProximityPrize.SubmissionLower.LocatorSourceArithmetic

/- One fixed A77 kernel suffices for every replacement cell. -/
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem auxiliary_rank : localRankBound 77 2567 23 = 139739440 :=
  LocatorSourceArithmetic.A77_fixed_rank

theorem auxiliary_nullity :
    coefficientCount 14002065 131071 2567 23 -
      262144 * localRankBound 77 2567 23 = 38456280382 :=
  LocatorSourceArithmetic.A77_fixed_nullity

theorem auxiliary_shape : 14002065 + 23 ≤ 131071 * (106 + 1) :=
  LocatorSourceArithmetic.A77_fixed_shape
theorem auxiliary_capacity :
    14002065 - 50775 ≤ (77 - 1) * 181845 + (131071 - 1) :=
  LocatorSourceArithmetic.A77_fixed_capacity

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
