import ProximityPrize.SubmissionLower.Scalar50Direct
import ProximityPrize.SubmissionLower.Scalar50LeadingLower

set_option Elab.async false
namespace Scalar50LeadingList

theorem scalar_list : CJ0.ScalarList 179915 2493026848761586 :=
  Scalar50Direct.of_lower fun _ _ _ hm => Scalar50LeadingLower.lower_count hm

#print axioms scalar_list
end Scalar50LeadingList
