import ProximityPrize.SubmissionLower.Scalar50Wide55Direct
import ProximityPrize.SubmissionLower.Scalar50Wide55Lower
import ProximityPrize.SubmissionLower.CurveListScalarWide55Rank

set_option Elab.async false
namespace Scalar50Wide55DirectList

theorem scalar_list : CJ0.ScalarList 179905 2002422605167821 :=
  Scalar50Wide55Direct.of_lower CurveListScalarWide55.prefix_bound
    fun t _ _ _ hm => Scalar50Wide55Lower.lower_count t hm

#print axioms scalar_list
end Scalar50Wide55DirectList
