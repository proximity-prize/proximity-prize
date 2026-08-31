import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
theorem kernelAmbient_rank:localRankBound 126 79970 39 = 19363347360 :=
  LocatorArithmetic.kernelC_rank
theorem kernelAmbient_nullity :
    coefficientCount 22901256 131071 79970 39 -
      262144 * localRankBound 126 79970 39 = 31194811929970 :=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
