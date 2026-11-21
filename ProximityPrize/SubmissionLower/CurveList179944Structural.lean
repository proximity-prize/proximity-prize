import ProximityPrize.SubmissionLower.StructuralListMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.CurveList179944StructuralRank

set_option Elab.async false
set_option maxRecDepth 18000

namespace CurveList179944Structural

open CJ0 CurveList179944StructuralRank
open private native_shape from ProximityPrize.SubmissionLower.CurveList179944StructuralRank

private theorem list_price : StructuralList.tariff 179944 source = 5983004930350854 := by
  decide +kernel

theorem scalar_list : ScalarList 179944 5983004930350854 := by
  have hA : AgreementOK 179944 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 72 := by
    intro j hj hcut
    have hq : j.q ≤ 71 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_shortening ShortenChart.shortenChart
    179944 source 123194 hA (by decide) native_shape (by decide) (by decide) surplus
    (Or.inr ⟨72, le_rfl, tail, prefix_bound⟩)
  rwa [list_price] at h

#print axioms scalar_list

end CurveList179944Structural
