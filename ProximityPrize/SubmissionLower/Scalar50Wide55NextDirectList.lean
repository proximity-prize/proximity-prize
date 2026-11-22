import ProximityPrize.SubmissionLower.Scalar50Wide55NextDirect
import ProximityPrize.SubmissionLower.Scalar50Wide55NextLower
import ProximityPrize.SubmissionLower.CurveListScalarWide55RankTight

namespace Scalar50Wide55NextDirectList

theorem scalar_list_tight : CJ0.ScalarList 179895 1710834581234467 :=
  Scalar50Wide55NextDirect.of_lower CurveListScalarWide55.prefix_bound_tight
    fun t _ _ _ hm => Scalar50Wide55NextLower.lower_count t hm

end Scalar50Wide55NextDirectList
