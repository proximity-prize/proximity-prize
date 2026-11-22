import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.KoalaScalarListSummary

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarList

open CJ0 KoalaScalarListBank

private theorem list_price : StructuralList.tariff 179886 source = 6965751486339445 := by decide +kernel

theorem scalar_list : ScalarList 179886 6965751486339445 := by
  have hA : AgreementOK 179886 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 75 := by
    intro j hj hcut
    have hq : j.q ≤ 74 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179886 source 145510 hA (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨75, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list
end KoalaScalarList
