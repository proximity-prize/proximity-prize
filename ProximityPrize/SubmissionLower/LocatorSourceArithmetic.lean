import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
theorem kernelAmbient_rank:localRankBound 102 40000 31 = 5111141216 :=
  LocatorArithmetic.kernelC_rank
theorem kernelAmbient_nullity :
    coefficientCount 18541152 131071 40000 31 -
      262144 * localRankBound 102 40000 31 = 6917788416568 :=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
