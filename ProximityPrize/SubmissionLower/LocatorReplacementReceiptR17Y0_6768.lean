import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Full6765
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r17_y0:
    ∀ y:Fin 79,0≤y.val→y.val<2→∀ b:Fin 160,
      Receipt ((⟨16,by decide⟩:Fin 17),y,b):=by decide
end ProximityPrize.SubmissionLower.LocatorReplacementData
