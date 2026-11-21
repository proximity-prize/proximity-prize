import ProximityPrize.SubmissionLower.StructuralListPairMain
import ProximityPrize.SubmissionLower.ShortenChart
import ProximityPrize.SubmissionLower.CurveList179925Witness

set_option Elab.async false
set_option maxRecDepth 18000

namespace CurveList179925Structural

open CJ0 CurveList179925Witness
open private native_shape from ProximityPrize.SubmissionLower.CurveList179925Witness

private theorem price : StructuralList.pairTariff 179925 source 142 39 19 = 5359055396082609 := by decide +kernel

theorem scalar_list : ScalarList 179925 5359055396082609 := by
  have hA : AgreementOK 179925 := ⟨by decide, by decide, by decide, by decide⟩
  have tail : SilentTail source 73 := by
    intro j hj hcut
    have hq : j.q ≤ 72 := (native_shape.support j hj).1
    omega
  have h := StructuralList.scalar_list_of_pair_shortening ShortenChart.shortenChart
    179925 source 130679 hA (by decide) native_shape (by decide) 142 39 19 (by unfold StructuralList.normalizedBand; decide)
    (by decide) (by decide) (by decide) (by decide) surplus
    (Or.inr ⟨73, le_rfl, tail, prefix_bound⟩)
  rwa [price] at h

#print axioms scalar_list

end CurveList179925Structural
