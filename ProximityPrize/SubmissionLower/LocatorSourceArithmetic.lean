import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302

theorem kernelAmbient_rank : localRankBound 95 40000 29 = 4156917435 :=
  LocatorArithmetic.kernelC_rank

theorem kernelAmbient_nullity :
    coefficientCount 17269670 131071 40000 29 -
      262144 * localRankBound 95 40000 29 = 5303371189990 :=
  LocatorArithmetic.kernelC_nullity

end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
