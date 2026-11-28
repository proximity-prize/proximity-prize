import ProximityPrize.SubmissionLower.Z6970H2307GateDispatch
import ProximityPrize.SubmissionLower.Z6970H2307CountAssembly
import ProximityPrize.SubmissionLower.Z6970H2307Orders
import ProximityPrize.SubmissionLower.Z6970H2307PointTable
import ProximityPrize.SubmissionLower.Z6970CompanionSound
import ProximityPrize.SubmissionLower.Z6970ExpandedHceilH2307Actual

namespace Height2307Count6970

theorem family_count {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179730 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2307) :
    Γ.card≤274779381266040420 :=
  count_with_table (Height2307GateDispatch.proof ExpandedOrderH2307.actual_hceil)
    (fun k x _ _ => Height2307Orders.order_valid k x)
    Height2307Companion.book_sound Height2307PointCertificates.pointTable
    ExpandedOrderH2307.actual_hceil M F lo hi

end Height2307Count6970
