import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.KoalaScalarListSummary

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarList

open CJ0 KoalaScalarListBank

private theorem list_price : StructuralList.tariff 179915 source = 6572474702329476 := by decide +kernel

theorem scalar_list : ScalarList 179915 6572474702329476 := by
  have hA : AgreementOK 179915 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 73 := by
    intro j hj hcut
    have hq : j.q ≤ 72 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179915 source 136484 hA (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨73, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end KoalaScalarList
