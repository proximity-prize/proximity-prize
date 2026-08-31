import ProximityPrize.SubmissionLower.LocatorReplacementReceiptUnitBarrier03
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_unit_ti_19:∀ p:{c:FineCell // HardFine c},
    Receipt (Sum.inr (Sum.inr (⟨p,(19:Fin 32)⟩:UnitCell))):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
