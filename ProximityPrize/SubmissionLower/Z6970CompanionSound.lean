import ProximityPrize.SubmissionLower.Z6970CompanionFromPrices
import ProximityPrize.SubmissionLower.Z6970CompanionOrdinary
import ProximityPrize.SubmissionLower.Z6970CompanionInvoice
import ProximityPrize.SubmissionLower.Z6970CompanionSupport
import ProximityPrize.SubmissionLower.Z6970H2307PointAPI

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace Height2307Companion
open K1_13 (Shape InBox)
open Height2307Orders (order lookup thresholds Threshold)
open Height2307Bands (Band start)
open Low6969RetainedCut (contractedPrice)
open scoped BigOperators

theorem book_sound : Height2307Allocation.Companion
    (fun k x => order k x.b x.j) (fun k r => book k.val r) := by
  intro k rest debt hbook n a cost partners valid fit paid
  apply with_ordinary_prices (order k) (fun x => Low6969Prices.physicalPriceOld x (order k x.b x.j))
    (supports_order k) (physical_corners _ (fun hb hj => monoLookup hb hj (thresholds k)))
    hbook _ fit.1 fit.2.1 fit.2.2 (fun i hi => (paid i hi).trans (contract_le_old _ _ _))
  intro i hi
  obtain ⟨⟨hT,hJ,hB⟩,hshape⟩ := valid i hi
  exact ⟨hT,hJ,by omega,hshape⟩

end Height2307Companion
