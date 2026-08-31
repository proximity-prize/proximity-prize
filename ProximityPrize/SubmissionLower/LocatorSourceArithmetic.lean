import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
theorem kernelAmbient_rank:localRankBound 114 40000 35 = 7153893720 :=
  LocatorArithmetic.kernelC_rank
theorem kernelAmbient_nullity :
    coefficientCount 20721324 131071 40000 35 -
      262144 * localRankBound 114 40000 35 = 10544200510155 :=
  LocatorArithmetic.kernelC_nullity
end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
