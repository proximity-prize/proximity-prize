import ProximityPrize.SubmissionLower.LocatorReplacementReceiptUnitBarrier01
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_unit_ti_9:∀ p:{c:FineCell // HardFine c},
    Receipt (Sum.inr (Sum.inr (⟨p,(9:Fin 32)⟩:UnitCell))):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
