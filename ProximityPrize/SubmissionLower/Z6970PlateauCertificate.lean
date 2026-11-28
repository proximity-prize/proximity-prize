import ProximityPrize.SubmissionLower.Z6970PlateauBridge
import ProximityPrize.SubmissionLower.Z6970PlateauTotal

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem certified_plateau : (∑ z : ExpandedPivotOpt6970.Column, ExpandedTaper6970.triangle z) ≤ 277161303086208 :=
  le_of_eq (global_sum.trans exact_plateau_sum)

end ExpandedPlateauSum6970
