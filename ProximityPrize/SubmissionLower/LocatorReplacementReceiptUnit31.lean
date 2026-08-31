import ProximityPrize.SubmissionLower.LocatorReplacementReceiptUnitBarrier06
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_unit_ti_31:∀ p:{c:FineCell // HardFine c},
    Receipt (Sum.inr (Sum.inr (⟨p,(31:Fin 32)⟩:UnitCell))):=by decide

end ProximityPrize.SubmissionLower.LocatorReplacementData
