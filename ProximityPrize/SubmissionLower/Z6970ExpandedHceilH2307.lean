import ProximityPrize.SubmissionLower.Z6970ExpandedOrderH2307
import ProximityPrize.SubmissionLower.Z6970ExpandedRankCombine
import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderData

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedOrderH2307
open ExpandedTaper6970
open scoped BigOperators

theorem hceil_of_plateau
    (hp : (∑ z : ExpandedPivotOpt6970.Column, triangle z) ≤ 277161303086208) :
    layerWidth * (21230822871131 - 1) < sourceRank :=
  certified_hceil (rank_budget_of_certificates hp exact_remainder_le)

end ExpandedOrderH2307
