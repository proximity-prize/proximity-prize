import ProximityPrize.SubmissionLower.LocatorReplacementDataCore
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem receipt_unit_r12:∀ c:UnitCell,unitR c=12→
    Receipt (Sum.inr (Sum.inr c)):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData

