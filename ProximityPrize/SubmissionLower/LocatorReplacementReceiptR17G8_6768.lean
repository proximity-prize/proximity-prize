import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR17G7_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r17_g8:∀ y:Fin 79,64≤y.val→y.val<72→∀ b:Fin 160,
    Receipt ((⟨16,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
